### ------
import signal, auxiliary, channel_func, math, warnings, sys, os
import threading, concurrent.futures
import random as rm
from threading import Lock

from typing import Any, Dict, Optional
from pathlib import Path
import json
from math import ceil
from sage.all import log, infinity, RR, ZZ, next_prime
from sage.graphs.generators.distance_regular import codes
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.coding.guruswami_sudan.gs_decoder import roth_ruckenstein_root_finder

from auxiliary import print_matrix_with_precision

# Flag to indicate if the program should stop
terminate_flag = threading.Event()
results_lock = Lock()

def signal_handler(sig, frame):
    print("KeyboardInterrupt caught. Terminating...")
    terminate_flag.set()  # Notify threads to terminate
    sys.exit(0)

# Register the signal handler
signal.signal(signal.SIGINT, signal_handler)

# Suppress specific deprecation warnings
warnings.filterwarnings("ignore", category=DeprecationWarning, module="sage")

def safe_update_and_write(file_path, index, simul_entry, data):
    try:
        with results_lock:
            # Update shared data
            data[index] = simul_entry
            data_to_write = {"Simul": [simul_entry.to_json() for simul_entry in data]}

            # Write to a temporary file and atomically replace
            temp_file_path = f"{file_path}.tmp"
            with open(temp_file_path, 'w') as temp_file:
                json.dump(data_to_write, temp_file, indent=4, cls=auxiliary.CustomEncoder)
            os.replace(temp_file_path, file_path)  # Atomic rename ensures safety
    except Exception as e:
        print(f"Error during file update: {e}")

def initialize(filename, simul_entry):
    file_path2 = Path(filename)
    if file_path2.exists():
        # Load existing data
        simul_list = auxiliary.read_json_file(filename)
        index = auxiliary.check_simulation_entry(simul_list, simul_entry)
        if index == -1:  # Add new entry if it doesn't exist
            index = len(simul_list)
            simul_list.append(simul_entry)

            try:
                auxiliary.write_json_file(filename, simul_list)  # Check if `simul_list` is serializable
            except TypeError as e:
                raise ValueError(f"simul_list contains non-serializable data: {e}")

            #auxiliary.write_json_file(filename, simul_list)  # Save the updated data back to the file
        else:
            simulation_result = simul_list[index]
            simul_entry.simulationResult = simulation_result
    else:
        auxiliary.create_default_json_file(filename, simul_entry)
        simul_list = auxiliary.read_json_file(filename)
        index = 0

    return simul_list, index

def simulate_safe_iteration(codeParams, channelParams, C, L, transmit_prob, transmit_prob_rev,
                            term1_vec, term1_vec_rev, td, ti, rM, completed_iterations, results_lock):
    r"""
        Simulates a single run of random message encoding, transmission & decoding.

        INPUT:
        - ``td`` -- number of deletions.
        - ``ti`` -- number of insertions.
        - ``rM`` -- number of received sequences.
        - ``L`` -- max list size.


    """
    while not terminate_flag.is_set():
        # RS code parameters
        q, n, k = codeParams.q, codeParams.n, codeParams.k
        eval_pts = codeParams.eval_pts

        # IDS channel parameters
        Pi, Pd, Ps = channelParams.pI, channelParams.pD, channelParams.pS

        GF_q = GF(q)
        # step 1: generate random message vector
        u = vector(GF_q, codeParams.k)
        for i in range(codeParams.k):
            u[i] = GF_q.random_element() #rm.randint(0, q - 1)

        # step 2: encode
        assert len(u) == codeParams.k, "well"
        G = C.generator_matrix() # Retrieve the generator matrix
        assert G.base_ring() == GF_q, "The generator matrix must be defined over the same field"

        codeword = C.encode(u)
        cl = codeword.list()

        # step 3: transmit over ID channel
        y_list = []
        for i in range(rM):
            received = channel_func.transmit(codeword, q, Pi, Pd, Ps)
            y_list.append(received)

        # assemble term1 & term1_rev according to the length of the received sequences
        term1, term1_rev = [], []
        for i in range(rM):
            net_drift =  len(y_list[i]) - n
            term1.append(term1_vec[net_drift + td])
            term1_rev.append(term1_vec_rev[net_drift + td])

        # step 4: compute reliability and multiplicity matrices
        #Pi_mat = auxiliary.get_reliability_matrix(q, n, received, Pi, Pd, Ps, term1, transmit_prob)
        Pi_mat = auxiliary.get_reliability_matrix_bi(q, n, y_list, Pi, Pd, Ps, term1, term1_rev, transmit_prob, transmit_prob_rev)
        M = auxiliary.get_multiplicity_matrix_L(Pi_mat, k, L)

        est_msg_list, est_codewords, success = auxiliary.kv_decode(y_list, C, eval_pts, q, k, M)

        # Results for this iteration
        iteration_result = {
            "numIterations": 1,
            "frameErrors": 0,
            "bitErrors": 0,
            "erasures": 0,
        }
        if len(est_codewords) == 0:
            iteration_result["erasures"] += 1
            iteration_result["frameErrors"] += 1
            iteration_result["bitErrors"] += k
        else: # in case of multiple outputs
            # pick the codeword that minimizes Levenshtein distance
            ind, ld = 0, math.inf
            for i in range(len(est_codewords)):
                ld1 = 0
                for y in y_list:
                    ld1 += auxiliary.levenshteinIterative(est_codewords[i], y)
                if ld1 < ld:
                    ind, ld = i, ld1

            if (est_codewords[ind] - codeword).hamming_weight() != 0:
                iteration_result["frameErrors"] += 1
                iteration_result["bitErrors"] += (est_msg_list[ind] - u).hamming_weight()

        with results_lock:
            completed_iterations[0] += 1

        return iteration_result

def simulate_one_iteration(codeParams, channelParams, C, L, transmit_prob, transmit_prob_rev,
                            term1_vec, term1_vec_rev, td, ti, rM):
    r"""
       Simulates a single run of random message encoding, transmission & decoding.

        INPUT:
        - ``td`` -- number of deletions.
        - ``ti`` -- number of insertions.
        - ``rM`` -- number of received sequences.
        - ``L`` -- list size.

    """
    # RS code parameters
    q, n, k = codeParams.q, codeParams.n, codeParams.k
    eval_pts = codeParams.eval_pts

    # IDS channel parameters
    Pi, Pd, Ps = channelParams.pI, channelParams.pD, channelParams.pS

    GF_q = GF(q)
    # step 1: generate random message vector
    u = vector(GF_q, codeParams.k)
    for i in range(codeParams.k):
        u[i] = GF_q.random_element() #rm.randint(0, q - 1)

    # step 2: encode
    assert len(u) == codeParams.k, "well"

    # Retrieve the generator matrix
    G = C.generator_matrix()
    assert G.base_ring() == GF_q, "The generator matrix must be defined over the same field"

    codeword = C.encode(u)
    cl = codeword.list()

    # step 3: transmit over ID channel
    y_list = []
    for i in range(rM):
        r"""indices_to_delete = rm.sample(range(n), td)
        received = [cl[i] for i in range(n) if i not in indices_to_delete]

        indices_to_insert = sorted(rm.sample(range(n - td + 1), ti)) #vector(GF_q, [cl[i] for i in range(n) if i not in indices_to_delete])
        for offset, idx in enumerate(indices_to_insert):
            received.insert(idx + offset, rm.randint(0, q - 1))

        received = vector(GF_q, received)"""
        received = channel_func.transmit(codeword, q, Pi, Pd, Ps)
        y_list.append(received)
        # assemble term1 & term1_rev according to the length of the received sequences
    term1, term1_rev = [], []
    for i in range(rM):
        net_drift = len(y_list[i]) - n
        term1.append(term1_vec[net_drift + td])
        term1_rev.append(term1_vec_rev[net_drift + td])

    # step 4: compute reliability and multiplicity matrices
    #Pi_mat = auxiliary.get_reliability_matrix(q, n, y_list, Pi, Pd, Ps, term1, transmit_prob)
    Pi_mat = auxiliary.get_reliability_matrix_bi(q, n, y_list, Pi, Pd, Ps, term1, term1_rev, transmit_prob, transmit_prob_rev) # <--------------- bidirectional
    M = auxiliary.get_multiplicity_matrix_L(Pi_mat, k, L) #auxiliary.get_multiplicity_matrix(Pi_mat, s)


    # step 5: soft interpolation
    est_msg_list, est_codewords, success = auxiliary.kv_decode(y_list, C, eval_pts, q, k, M)

    # Results for this iteration
    iteration_result = {
        "numIterations": 1,
        "frameErrors": 0,
        "bitErrors": 0,
        "erasures": 0,
    }

    if len(est_codewords) == 0:
        iteration_result["erasures"] += 1
        iteration_result["frameErrors"] += 1
        iteration_result["bitErrors"] += k
        #print("\nFailed\n")
        print("Decoding failure")
    else:
        # pick the codeword that minimizes Levenshtein distance
        ind, ld = 0, math.inf
        for i in range(len(est_codewords)):
            ld1 = 0
            for y in y_list:
                ld1 += auxiliary.levenshteinIterative(est_codewords[i], y)
            if ld1 < ld:
                ind, ld = i, ld1

        if (est_codewords[ind] - codeword).hamming_weight() != 0:
            iteration_result["frameErrors"] += 1
            iteration_result["bitErrors"] += (est_msg_list[ind] - u).hamming_weight()

        print(f"transmitted: {cl}")
        print(f"received:")
        for y in y_list:
            print(y)
        print(f"KV decoder output:")
        for cw in est_codewords:
            print(cw)

    return iteration_result

def findCode(n, k):
    """
       Finds the evaluation points from the file in the `FoundCodes` folder
       that matches the given n, k, and ta.

       Parameters:
       - n (int): The value of n.
       - k (int): The value of k.

       Returns:
       - q (int): The value of q from the matching entry.
       - eval_pts (list): The evaluation points from the matching entry.
    """
    filename = f"FoundCodes/results_n{n}_k{k}.txt"

    if not os.path.isfile(filename): # no adversarial code found
        print(f"No adversarial code found in FoundCodes")
        filename = f"FoundCodes/results_n{n}_k{k}.txt"

        if not os.path.isfile(filename): # no existing code found
            # creating new primitive code
            q = next_prime(n)
            n = q - 1

            gfq = GF(q, modulus='primitive')
            prim_el = gfq.gen()

            eval_pts = [prim_el ** i for i in range(n)]
            assert n == len(set(eval_pts))

            # Open the file in append mode; it will be created if it doesn't exist
            with open(filename, "a") as file:
                file.write(f"n: {n}, k: {k}, q: {q}\nEval pts: {eval_pts}\n\n")

            print("Chose eval_pts = ", eval_pts)
            return q, eval_pts  # Convert elements to integers

        else: # loading existing primitive code
            with open(filename, "r") as file:
                lines = file.readlines()

            for line in lines:
                if line.startswith("n:"):
                    # Extract the parameters from the line
                    parts = line.strip().split(", ")
                    entry_n = int(parts[0].split(":")[1].strip())
                    entry_k = int(parts[1].split(":")[1].strip())
                    q = int(parts[2].split(":")[1].strip())
                    GF_q = GF(q)

                    eval_line = next((l for l in lines[lines.index(line) + 1:] if l.startswith("Eval pts:")), None)
                    if eval_line:
                        eval_pts = eval(eval_line.split(":")[1].strip())  # Safely evaluate the list
                        eval_pts = [GF_q(el) for el in eval_pts]
                        print("Chose eval_pts = ", eval_pts)
                        return q, eval_pts  # Convert elements to integers

    else:
        with open(filename, 'r') as file:
            lines = file.readlines()

        for line in lines:
            if line.startswith("n:"):
                # Extract the parameters from the line
                parts = line.strip().split(", ")
                entry_n = int(parts[0].split(":")[1].strip())
                entry_k = int(parts[1].split(":")[1].strip())
                q = int(parts[2].split(":")[1].strip())
                GF_q = GF(q)
                # Match the required t
                if entry_n == n and entry_k == k:
                    # Get the next line for eval points
                    eval_line = next((l for l in lines[lines.index(line) + 1:] if l.startswith("Eval pts:")), None)
                    if eval_line:
                        eval_pts = eval(eval_line.split(":")[1].strip())  # Safely evaluate the list
                        eval_pts = [GF_q(el) for el in eval_pts]

                        print("Chose eval_pts = ", eval_pts)

                        return q, eval_pts  # Convert elements to integers

    # If no matching entry is found
    raise ValueError(f"No entry found with n={n}, k={k} in FoundCodes")


def main():
    numIter = int(5000)
    if len(sys.argv) == 8:
        n, k = map(int, sys.argv[1:3])
        rM = int(sys.argv[3])
        Pi, Pd = map(float, sys.argv[4:6])
        L = int(sys.argv[6])
        folder_name = sys.argv[7]
    else:
        # Fallback to manual input if arguments are not provided
        n, k = map(int, input("Enter n, k separated by space: ").split())
        rM = int(input("Enter #received sequences: "))
        Pi, Pd = map(float, input("Enter pI, pD separated by space: ").split())
        L = int(input("Enter list size: "))
        folder_name = "Sim"

    q, eval_pts = findCode(n, k)
    n = len(eval_pts)

    C = codes.GeneralizedReedSolomonCode(eval_pts, k)  # eval points, dimension
    code_param = auxiliary.CodeParams(q, n, k, eval_pts)

    # ----------------- Choose channel parameters -----------------------
    #Pi, Pd, Ps = ti / n, td / n, 0.0
    ti, td = round(ceil(Pi * n) * 1.8), round(ceil(Pd * n) * 1.8 )
    Ps = 0.0

    channel_param = auxiliary.ChannelParams(Pi, Pd, Ps)

    transmit_prob = channel_func.get_transmit_probabilities(q, n + 20, n, channel_param.pI, channel_param.pD)
    transmit_prob_rev = channel_func.get_transmit_probabilities(q, n + 20, n, channel_param.pI, channel_param.pD)

    term1_vec, term1_vec_rev = [], []
    for i in range(-td, ti + 1):
        term1_vec.append(auxiliary.get_term_vector(q, n, n + i, Pi, Pd, transmit_prob))
        term1_vec_rev.append(auxiliary.get_term_vector(q, n, n + i, Pi, Pd, transmit_prob_rev))


    # ------------------ Auxiliary variables ------------------------------
    simulation_result = auxiliary.SimulationResults()
    simul_entry = auxiliary.Simul(channel_param, simulation_result, L, rM)#s)

    file_path = folder_name + f"/RS_{q}_{n}_{k}.json"
    data, index = initialize(file_path, simul_entry)
    simul_entry = data[index]

    numIterations = simul_entry.simulationResult.numIterations
    frameErrors, bitErrors = simul_entry.simulationResult.frameErrors, simul_entry.simulationResult.bitErrors
    erasures = simul_entry.simulationResult.erasures
    # ====================================================================

    print(f"\nCode parameters: n = {code_param.n}, k = {code_param.k}.")
    print("Eval. points: ", C.evaluation_points())
    print(f"Channel parameters: pI = {Pi}, pD = {Pd}, pS = {Ps}; list size = {L}; M = {rM}")

    # Thread-safe counter for completed iterations
    completed_iterations = [0]
    results_lock = threading.Lock()

    # Create a ThreadPoolExecutor
    try:
        with concurrent.futures.ThreadPoolExecutor() as executor:
            futures = [executor.submit(simulate_safe_iteration, code_param, channel_param, C, L, transmit_prob, transmit_prob_rev,
                                       term1_vec, term1_vec_rev, td, ti, rM, completed_iterations, results_lock) for i in range(numIter)]

            for future in concurrent.futures.as_completed(futures):
                try:
                    iteration_result = future.result()

                    with results_lock:
                        numIterations += iteration_result["numIterations"]
                        frameErrors += iteration_result["frameErrors"]
                        bitErrors += iteration_result["bitErrors"]
                        erasures += iteration_result["erasures"]

                        completed = completed_iterations[0]
                        FER = frameErrors / numIterations if numIterations else 0
                        BER = bitErrors / (numIterations * code_param.k) if numIterations else 0
                        ER_p = erasures / numIterations if numIterations else 0

                        simul_entry.simulationResult = auxiliary.SimulationResults(numIterations, frameErrors, bitErrors, erasures, FER, BER, ER_p)

                        safe_update_and_write(file_path, index, simul_entry, data)

                        progress = 100 * completed / numIter
                        print(f"\rProgress: {progress:.2f}%  FER: {FER} BER: {BER} Erasure prob.: {ER_p}", end='', flush=True)
                except Exception as e:
                    print(f"Error in task: {e}")
    except KeyboardInterrupt:
        print("\nExecution interrupted by user. Shutting down...")
    except Exception as e:
        print(f"An error occurred: {e}")
    print("\n--------------------------------------------------------------")
    
    print(f"\nRS[{code_param.n}, {code_param.k}]_{q} code")
    print(f"Channel: {td} dels, {ti} insertions, list size = {L}, M = {rM}") # s = {s}")
    print(f"\nBER: {BER} FER: {FER} Erasure prob.: {ER_p}")
    print("--------------------------------------------------------------\n")


if __name__ == "__main__":
    main()
