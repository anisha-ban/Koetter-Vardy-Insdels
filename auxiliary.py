import json, math, copy, heapq, os
from sage.graphs.generators.distance_regular import codes
from sage.all import log, infinity
from sage.all import binomial
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.all import RR, ZZ, Integer, binomial
from sage.coding.guruswami_sudan.gs_decoder import roth_ruckenstein_root_finder, alekhnovich_root_finder
from sage.coding.guruswami_sudan.utils import johnson_radius
from six import print_

import channel_func, rs_codes
import random as rm

def print_matrix_with_precision(mat, precision=2):
    rows, cols = mat.nrows(), mat.ncols()
    format_str = f"{{:.{precision}f}}"
    for i in range(rows):
        row = [format_str.format(mat[i, j]) for j in range(cols)]
        print(" ".join(row))

def normalize_matrix_col(q, n, mat):
    # mat is a matrix with q rows, n columns, entries in log domain (log of probabilities)
    # Output: mat2 with entries such that each column sums up to 1

    mat2 = copy.deepcopy(mat)

    for t in range(n):
        max1 = max(mat2[i, t] for i in range(q))

        # Compute the term using the log-sum-exp trick
        term_f = sum(math.exp(mat2[i, t] - max1) if mat2[i, t] != -math.inf else 0.0 for i in range(q))

        # Normalize Pi_mat[i, t] after computing the term
        for i in range(q):
            mat2[i, t] = math.exp(mat2[i, t] - max1) / term_f if mat2[i, t] != -math.inf else 0.0

    return mat2


def print_reliability_matrix(Pi_mat, precision=2):
    q, n = Pi_mat.nrows(), Pi_mat.ncols()
    format_str = f"{{:.{precision}f}}"

    print("    ".join([str(i) for i in range(-1, n)]))
    for i in range(q):
        row = [str(i)] + [format_str.format(Pi_mat[i, j]) for j in range(n)]
        print(" ".join(row))

    print("\nSum: \n")
    sums = [sum([Pi_mat[i,t] for i in range(q)]) for t in range(n)]
    sums = [format_str.format(s) for s in sums]
    print(" ".join(sums))

def log_add(a, b):
    if a == -math.inf or b == -math.inf:
        return max(a,b)
    return max(a,b) + math.log(1 + math.exp(-abs(a-b)))

def log_sub(a, b):
    if b == -math.inf or a == -math.inf:
        return a

    diff = a - b
    if diff > 700:
        return a
    if diff < 1e-10:
        return b + math.log(math.expm1(diff))

    #print(f"{a}, {b}")

    return b + math.log(math.exp(diff) - 1)

def levenshteinIterative(ar1, ar2):
    r"""
        Returns the Levenshtein distance between ar1 & ar2.
    """
    m = len(ar1)
    n = len(ar2)

    # Create a 2D array (m+1) x (n+1)
    dp = [[0] * (n + 1) for _ in range(m + 1)]

    # Initialize the first row and first column
    for i in range(m + 1):
        dp[i][0] = i
    for j in range(n + 1):
        dp[0][j] = j

    # Fill the rest of the dp array
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            if ar1[i - 1] == ar2[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                dp[i][j] = 1 + min(dp[i - 1][j],    # Remove
                                   dp[i][j - 1]#,    # Insert
                                   #dp[i - 1][j - 1] # Replace
                                  )

    # The last element of the array is the Levenshtein distance
    return dp[m][n]



def get_cost_multiplicity(M):
    r"""
        Returns cost of multiplicity matrix (Def. 3, Koetter-Vardy TIT). This indicates the total number of linear constraints.
        #Returns min. score of codewords reqd as per Definition 12.3.2 (Essential Coding Theory, Guruswami, Rudra, Sudan).

        INPUT:
        - ``k`` -- dimension of RS code.
        - ``M`` -- multiplicity matrix.

    """

    """
    n, q = M.ncols(), M.nrows()
    sum1 = 0

    for i in range(n):
        for j in range(q):
            if M[j, i] > 0:
                sum1 += (M[j, i] * (M[j, i] + 1) / 2)
    """

    nonzero_entries = [M[i, j] for i in range(M.nrows()) for j in range(M.ncols()) if M[i, j] > 0]  # Filter out positive entries
    cost = sum(e * (e + 1) // 2 for e in nonzero_entries)

    #if sum1 != cost:
    #    print("here")

    return cost

class SimulationResults:
    def __init__(self, numIterations=0, frameErrors=0, bitErrors=0, erasures=0, FER=0.0, BER=0.0, ER_p=0.0):
        self.numIterations = numIterations
        self.frameErrors = frameErrors
        self.bitErrors = bitErrors
        self.erasures = erasures
        self.FER = FER
        self.BER = BER
        self.ER_p = ER_p

    @staticmethod
    def from_json(js):
        result = SimulationResults()
        result.numIterations = js['numIterations']
        result.frameErrors = js['frameErrors']
        result.bitErrors = js['bitErrors']
        result.erasures = js['erasures']
        result.FER = js['FER']
        result.BER = js['BER']
        result.ER_p = js['erasure_prob']
        return result

    def to_json(self):
        return {
            "numIterations": self.numIterations,
            "frameErrors": self.frameErrors,
            "bitErrors": self.bitErrors,
            "erasures": self.erasures,
            "FER": self.FER,
            "BER": self.BER,
            "erasure_prob": self.ER_p
        }

class ChannelParams:
    def __init__(self, pI=0.0, pD=0.0, pS=0.0):
        self.pI = pI
        self.pD = pD
        self.pS = pS

    @staticmethod
    def from_json(js):  # Make this a static method
        channel_param = ChannelParams()
        channel_param.pI = js['pI']
        channel_param.pD = js['pD']
        channel_param.pS = js['pS']
        return channel_param

    def to_json(self):
        assert (1.0 > self.pI >= 0.0
                and 1.0 > self.pD >= 0.0 and 1.0 > self.pS >= 0.0 and
                1.0 > self.pI + self.pD > 0.0)
        return {
            "pI": self.pI,
            "pD": self.pD,
            "pS": self.pS
        }

class CodeParams:
    def __init__(self, q=0, n=0.0, k=0.0, eval_pts=[]):
        self.q = q
        self.n = n
        self.k = k
        self.eval_pts = eval_pts

class Simul:
    def __init__(self, channelParam=None, simulationResult=None, L=5, rM=1):
        self.channelParam = channelParam if channelParam else ChannelParams()
        self.simulationResult = simulationResult if simulationResult else SimulationResults()
        self.L = L
        self.rM = rM

    def from_json(self, js):
        if not all(key in js for key in ['simulationResult', 'channelParam', 'L', 'rM']):
            raise ValueError("Missing keys in JSON data")
        channel_param = ChannelParams.from_json(js['channelParam'])
        simulation_result = SimulationResults.from_json(js['simulationResult'])
        return Simul(channelParam=channel_param, simulationResult=simulation_result, L=js['L'], rM=js['rM'])

    def to_json(self):
        return {
            "simulationResult": self.simulationResult.to_json(),
            "channelParam": self.channelParam.to_json(),
            "L": self.L,
            "rM": self.rM
        }

# Read JSON file
def read_json_file(filename):
    simul_list = []

    # Read the JSON file
    with open(filename, 'r') as file:
        data = json.load(file)

    # Parse the JSON data and create Simul objects
    for item in data['Simul']:
        simul = Simul()
        simul = simul.from_json(item)
        simul_list.append(simul)

    return simul_list


class CustomEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, Simul):
            return obj.to_json()  # Use the `to_json` method for Simul objects
        elif isinstance(obj, ChannelParams):
            return obj.to_json()  # Use the `to_json` method for ChannelParams objects
        elif isinstance(obj, SimulationResults):
            return obj.to_json()  # Use the `to_json` method for SimulationResults objects
        return super().default(obj)

def write_json_file(file_path, data):
    temp_file_path = f"{file_path}.tmp"
    with open(temp_file_path, 'w') as temp_file:
        json.dump(data, temp_file, indent=4, cls=CustomEncoder)
    os.replace(temp_file_path, file_path)

# Function to check if a simulation entry exists
def check_simulation_entry(data, target_simul):
    for i in range(len(data)):
        simul = data[i]
        if simul.L == target_simul.L and simul.rM == target_simul.rM and simul.channelParam.pI == target_simul.channelParam.pI and simul.channelParam.pD == target_simul.channelParam.pD and simul.channelParam.pS == target_simul.channelParam.pS:
            return i

    return -1


def create_default_json_file(filename, default_simul):
    json_data = {"Simul": [default_simul.to_json()]}
    try:
        with open(filename, 'w') as file:
            json.dump(json_data, file, indent=4, cls=CustomEncoder)
            print(f"Created JSON file: {filename}")
    except IOError as e:
        print(f"Error creating JSON file: {filename}\n{e}")



## ----------------------- KOETTER - VARDY functions ----------------------------------------------
def get_reliability_matrix_old(q, n, y, pI, pD, pS, drift_prob):
    r"""
            Generates reliability matrix (dimension q x n) for the Koetter-Vardy algorithm, where q is the field size
            and n is the block length.

            The (i, j)-th entry of this matrix represents the probability that the j-th transmitted symbol equals the
            i-th field element, given the received sequence y.

            INPUT:
            - ``q`` -- field size.
            - ``n`` -- block length of RS code.
            - ``pI`` -- insertion probability.
            - ``pD`` -- deletion probability.
            - ``pS`` -- substitution probability.

            OUTPUT:
            - ``Pi_mat`` -- reliability matrix.
    """
    ylen = len(y)

    # expected drift after transmission of 1 symbol (Davey-MacKay channel model)
    ED1 = pI / (1 - pI) - pD
    # variance of drift after transmission of 1 symbol (Davey-MacKay channel model)
    var_D1 = pI / (1 - pI) ** 2 + 2 * pI * pD / (1 - pI) + pD - pD ** 2

    # Since drift after transmission of T bits is a random variable that can be seen as the sum of
    # T iid random variables, each of which models the drift after transmission of 1 bit, we use the linearity of
    # expectation and variance, to limit the scope of our computations. More explicitly, we imagine that the i-th
    # transmitted bit, with high probability, corresponds to a window of symbols in the received sequence. This window
    # is centered at `expected_num_received_bits` (computed using expected drift). The length of the window is chosen as
    # 10 * (variance of drift after transmission of i bits).

    Pi_mat = matrix(RR, [[pD / q] * n for _ in range(q)])

    # place window around possible drift
    for t in range(1, n + 1):

        expected_num_received_bits = (1 + ED1) * t
        lower_bound_num_received = max(1, math.floor(expected_num_received_bits - 5 * t * var_D1))
        upper_bound_num_received = min(ylen, math.ceil(expected_num_received_bits + 5 * t * var_D1))

        for r in range(lower_bound_num_received, upper_bound_num_received + 1):
            # Recall that drift_prob[t, r] -> prob that t bits were transmitted while r were received

            for alpha in GF(q):
                if y[r - 1] == alpha:
                    term = drift_prob[t - 1, r - 1] + log((1 - pS) * (1 - pI - pD)) # changed expression here
                else:
                    term = drift_prob[t - 1, r - 1] + log(pS * (1 - pI - pD) / (q - 1)) # changed expression here

                # print("coordinates in Pi_mat", int(alpha)," ", t - 1)
                #Pi_mat[Integer(alpha), t - 1] = Pi_mat[Integer(alpha), t - 1] + exp(term)
                Pi_mat[int(alpha), t - 1] = Pi_mat[int(alpha), t - 1] + math.exp(term)

    # normalize each column of Pi_mat
    for t in range(n):
        term = 0.0

        for i in range(q):
            term = term + Pi_mat[i, t]

        for i in range(q):
            Pi_mat[i, t] = Pi_mat[i, t] / term

    return Pi_mat

def get_term_vector(q, n, ylen, pI, pD, transmit_prob):
    r"""
        Generates vector `term1` for the first summation terms in \pi_{i,j}.

        The vector `term1` (length n) has its i-th entry equals \sum_{r=1}^{R_ylen} F(i-1,r-1).F(n-i,ylen-r+1)

        INPUT:
        - ``n`` -- block length of RS code.
        - ``ylen`` -- length of received vector.
        - ``pI`` -- insertion probability.
        - ``pD`` -- deletion probability.
        - ``y_list`` -- list of received sequences

        OUTPUT:
        - ``term1``

    """
    term1 = [-math.inf for _ in range(n)]
    win = 20
    # expected drift after transmission of 1 symbol (Davey-MacKay channel model)
    ED1 = pI / (1 - pI) - pD
    # variance of drift after transmission of 1 symbol (Davey-MacKay channel model)
    var_D1 = pI / (1 - pI) ** 2 + 2 * pI * pD / (1 - pI) + pD - pD ** 2

    for t in range(1, n + 1):
        if t < n: # for each transmitted bit except last
            for r in range(1, ylen + 1):
                prior_received_symbols = transmit_prob[t - 1, r - 1] # y_1^{r-1} given t-1 transmitted symbols
                subsequent_received_symbols = log_sub(transmit_prob[n - t, ylen - r + 1], transmit_prob[n - t, ylen - r] + log(pI / q))
                term1[t - 1] = log_add(term1[t - 1], prior_received_symbols + subsequent_received_symbols)

            # for final term, when all symbols were received in part1
            prior_received_symbols = transmit_prob[t - 1, ylen]  # all of y received given t-1 transmitted symbols
            subsequent_received_symbols = (n - t) * log(pD) # all subsequent symbols deleted
            term1[t - 1] = log_add(term1[t - 1], prior_received_symbols + subsequent_received_symbols)
        else: # final transmitted bit
            for r in range(1, ylen + 2):
                term1[t - 1] = log_add(term1[t - 1], transmit_prob[t - 1, r - 1])

    return term1


def get_reliability_matrix(q, n, y_list, pI, pD, pS, term1, transmit_prob):
    r"""
        Generates reliability matrix (dimension q x n) for the Koetter-Vardy algorithm, where q is the field size
        and n is the block length.

        The (i, j)-th entry of this matrix represents the probability that the j-th transmitted symbol equals the
        i-th field element, given the received sequence y.

        INPUT:
        - ``q`` -- field size.
        - ``n`` -- block length of RS code.
        - ``pI`` -- insertion probability.
        - ``pD`` -- deletion probability.
        - ``pS`` -- substitution probability.
        - ``y_list`` -- list of received sequences
        - ``term1`` -- list (length = #received sequences) of vectors where the i-th entry equals log(term1) / Pd in equation \pi_{i,j} * q * P(y)

        OUTPUT:
        - ``Pi_mat`` -- reliability matrix.
    """
    num_received = len(y_list)

    # stores length of each received sequence
    ylen = [len(y) for y in y_list]

    pT = 1 - pI - pD
    # expected drift after transmission of 1 symbol (Davey-MacKay channel model)
    ED1 = pI / (1 - pI) - pD
    # variance of drift after transmission of 1 symbol (Davey-MacKay channel model)
    var_D1 = pI / (1 - pI) ** 2 + 2 * pI * pD / (1 - pI) + pD - pD ** 2

    # Since drift after transmission of T bits is a random variable that can be seen as the sum of
    # T iid random variables, each of which models the drift after transmission of 1 bit, we use the linearity of
    # expectation and variance, to limit the scope of our computations. More explicitly, we imagine that the i-th
    # transmitted bit, with high probability, corresponds to a window of symbols in the received sequence. This window
    # is centered at `expected_num_received_bits` (computed using expected drift). The length of the window is chosen as
    # 10 * (variance of drift after transmission of i bits).

    # list of reliability matrices: 1 for each received sequence
    Pi_mat_list = [matrix(RR, [[-math.inf] * n for _ in range(q)]) for _ in range(num_received)]

    for mi in range(num_received):
        for t in range(1, n + 1):  # for each transmitted bit
            term1_constant = term1[mi][t - 1] + log(pD)

            expected_num_received_bits = (1 + ED1) * t
            lower_bound_num_received = max(1, math.floor(expected_num_received_bits - 5 * t * var_D1))
            upper_bound_num_received = min(ylen[mi], math.ceil(expected_num_received_bits + 5 * t * var_D1))

            # considering window around expected drift
            for alpha in GF(q):
                term2 = -math.inf

                for r in range(lower_bound_num_received, upper_bound_num_received + 1):
                    if y_list[mi][r - 1] == alpha:
                        term2 = log_add(term2, transmit_prob[t - 1, r - 1] + transmit_prob[n - t, ylen[mi] - r] + log(1 - pS))
                    else:
                        term2 = log_add(term2, transmit_prob[t - 1, r - 1] + transmit_prob[n - t, ylen[mi] - r] + log(pS / (q - 1)))

                Pi_mat_list[mi][int(alpha), t - 1] = log_add(term1_constant, term2 + log(pT))

    # combined reliability matrix (initialized with 1 in each entry)
    Pi_mat = matrix(RR, [[0] * n for _ in range(q)])

    # multiply all matrices, i.e., add in log domain
    # weight each with 1 / P(y_i), where P(y_i) = P(receiving |y_i| symbols after transmitting n symbols) * q^{-|y_i|}
    for mi in range(num_received):
        prob_y = transmit_prob[n, ylen[mi]]
        for i in range(q):
            for t in range(n):
                Pi_mat[i, t] += Pi_mat_list[mi][i, t] - prob_y

    # normalize each column of Pi_mat (in log form)
    for t in range(n):
        # Find the maximum value in the column for numerical stability
        max_Pi = max(Pi_mat[i, t] for i in range(q))

        # Compute the term using the log-sum-exp trick
        term = sum(math.exp(Pi_mat[i, t] - max_Pi) for i in range(q))

        # Normalize Pi_mat[i, t] after computing the term
        for i in range(q):
            Pi_mat[i, t] = math.exp(Pi_mat[i, t] - max_Pi) / term

    return Pi_mat # (in scale 0-1)

def get_reliability_matrix_bi(q, n, y_list, pI, pD, pS, term1, term1_rev, transmit_prob, transmit_prob_rev):
    r"""
        Generates reliability matrix (dimension q x n) for the Koetter-Vardy algorithm, where q is the field size
        and n is the block length.

        The (i, j)-th entry of this matrix represents the probability that the j-th transmitted symbol equals the
        i-th field element, given the received sequence y.

        This function uses get_reliability_matrix() as a helper function.

        INPUT:
        - ``q`` -- field size.
        - ``n`` -- block length of RS code.
        - ``pI`` -- insertion probability.
        - ``pD`` -- deletion probability.
        - ``pS`` -- substitution probability.
        - ``y_list`` -- list of received sequences
        - ``transmit_prob`` -- matrix of dimension (xlen + 1) x (ylen + 1). (I,J)th entry denotes probability of
                            receiving a specific vector of J symbols and transmitting any I symbols, where I \in \{0, ..., xlen\} &
                            J \in \{0, ..., ylen\}
        - ``transmit_prob_rev`` -- matrix of dimension (xlen + 1) x (ylen + 1). Same as transmit_prob, but considers state
                                diagram of transmission from reverse direction

        OUTPUT:
        - ``Pi_mat`` -- reliability matrix.
    """
    num_received = len(y_list)

    # stores length of each received sequence
    ylen = [len(y) for y in y_list]

    pT = 1 - pI - pD
    # expected drift after transmission of 1 symbol (Davey-MacKay channel model)
    ED1 = pI / (1 - pI) - pD
    # variance of drift after transmission of 1 symbol (Davey-MacKay channel model)
    var_D1 = pI / (1 - pI) ** 2 + 2 * pI * pD / (1 - pI) + pD - pD ** 2
    w = 20
    # Since drift after transmission of T bits is a random variable that can be seen as the sum of
    # T iid random variables, each of which models the drift after transmission of 1 bit, we use the linearity of
    # expectation and variance, to limit the scope of our computations. More explicitly, we imagine that the i-th
    # transmitted bit, with high probability, corresponds to a window of symbols in the received sequence. This window
    # is centered at `expected_num_received_bits` (computed using expected drift). The length of the window is chosen as
    # 10 * (variance of drift after transmission of i bits).

    # list of reliability matrices: 1 for each received sequence
    Pi_mat_list_fwd = [matrix(RR, [[-math.inf] * n for _ in range(q)]) for _ in range(num_received)]
    Pi_mat_list_bwd = [matrix(RR, [[-math.inf] * n for _ in range(q)]) for _ in range(num_received)]

    for mi in range(num_received):
        for t in range(1, n + 1):  # for each transmitted bit
            term1_constant = term1[mi][t - 1] + log(pD)
            term1_rev_constant = term1_rev[mi][t - 1] + log(pD)

            expected_num_received_bits = (1 + ED1) * t
            lower_bound_num_received = max(1, math.floor(expected_num_received_bits - w * t * var_D1))
            upper_bound_num_received = min(ylen[mi], math.ceil(expected_num_received_bits + w * t * var_D1))

            # considering window around expected drift
            for alpha in GF(q):
                term2, term2_rev = -math.inf, -math.inf

                for r in range(lower_bound_num_received, upper_bound_num_received + 1):
                    # forward
                    prior_received_symbols = transmit_prob[t - 1, r - 1]
                    subsequent_received_symbols = log_sub(transmit_prob[n - t, ylen[mi] - r],
                                                          transmit_prob[n - t, ylen[mi] - r - 1] + log(pI / q)) if t < n else 0.0
                    prob_modifier = log(1 - pS) if y_list[mi][r - 1] == alpha else log(pS / (q - 1))

                    term2 = log_add(term2, prior_received_symbols + subsequent_received_symbols + prob_modifier)


                    # backward
                    prior_received_symbols = transmit_prob_rev[t - 1, r - 1]
                    subsequent_received_symbols = log_sub(transmit_prob_rev[n - t, ylen[mi] - r],
                                                          transmit_prob_rev[n - t, ylen[mi] - r - 1] + log(pI / q)) if t < n else 0.0
                    prob_modifier = log(1 - pS) if y_list[mi][-(r - 1) - 1] == alpha else log(pS / (q - 1))
                    term2_rev = log_add(term2_rev, prior_received_symbols + subsequent_received_symbols + prob_modifier)

                Pi_mat_list_fwd[mi][int(alpha), t - 1] = log_add(term1_constant, term2 + log(pT))
                Pi_mat_list_bwd[mi][int(alpha), t - 1] = log_add(term1_rev_constant, term2_rev + log(pT))

    # combined reliability matrix (initialized with 1 in each entry)
    Pi_mat_fwd = matrix(RR, [[0] * n for _ in range(q)])
    Pi_mat_bwd = matrix(RR, [[0] * n for _ in range(q)])

    # multiply all matrices, i.e., add in log domain
    # weight each with 1 / P(y_i), where P(y_i) = P(receiving |y_i| symbols after transmitting n symbols) * q^{-|y_i|}
    for mi in range(num_received):
        prob_y1 = log_sub(transmit_prob[n, ylen[mi]], transmit_prob[n, ylen[mi] - 1] + log(pI / q))
        prob_y2 = log_sub(transmit_prob_rev[n, ylen[mi]], transmit_prob_rev[n, ylen[mi] - 1] + log(pI / q))
        for i in range(q):
            for t in range(n):
                Pi_mat_fwd[i, t] += Pi_mat_list_fwd[mi][i, t] - prob_y1
                Pi_mat_bwd[i, t] += Pi_mat_list_bwd[mi][i, t] - prob_y2

    # normalize each column of Pi_mat (in log form)
    Pi_mat_fwd = normalize_matrix_col(q, n, Pi_mat_fwd)
    Pi_mat_bwd = normalize_matrix_col(q, n, matrix(RR, [row[::-1] for row in Pi_mat_bwd.rows()]))

    # average fwd & bwd matrices
    Pi_mat = matrix(RR, [[(Pi_mat_fwd[r, c] + Pi_mat_bwd[r, c]) / 2  for c in range(n)] for r in range(q)])

    return Pi_mat

def get_multiplicity_matrix(Pi_mat, s):
    r"""
        Generates multiplicity matrix (dimension q x n) for the Koetter-Vardy algorithm, where q is the field size
        and n is the block length.

        The (i, j)-th entry of this matrix can be thought of as a weight for the i-th field element. This weight is high
        if the probability that the j-th transmitted symbol equals the i-th field element (given the received sequence y),
        is high.

        Implemented using Algorithm A in [Koetter, Vardy, T-IT 2003].

        INPUTS:
        - ``Pi_mat`` -- reliability matrix.
        - ``s`` -- positive integer, total num. of interpolation points.

        OUTPUT:
        - ``M`` -- multiplicity matrix.

    """
    Pi_mat_copy = copy.deepcopy(Pi_mat)
    Pi_star = Pi_mat_copy

    q, n = Pi_mat_copy.dimensions()
    M = matrix(q, n, 0)  # hopefully this is all zeros

    # Create a max-heap for elements in Pi_star
    heap = []
    for i in range(q):
        for j in range(n):
            heapq.heappush(heap, (-Pi_star[i, j], i, j))  # Push negative to simulate max-heap

    while s > 0:
        # Pop the maximum element
        pi_max, imax, jmax = heapq.heappop(heap)
        pi_max = -pi_max  # Convert back to positive

        Pi_star[imax, jmax] = Pi_mat_copy[imax, jmax] / (M[imax, jmax] + 2)
        M[imax, jmax] += 1
        s -= 1

        # Push the updated element back into the heap
        heapq.heappush(heap, (-Pi_star[imax, jmax], imax, jmax))

    return M

def get_multiplicity_matrix_L(Pi_mat, k, L):
    r"""
        Generates multiplicity matrix (dimension q x n) for the Koetter-Vardy algorithm, where q is the field size
        and n is the block length. (such that #codewords produced by decoder <= L)

        Works in accordance with eq.(18) [Koetter, Vardy, T-IT 2003]

        INPUTS:
        - ``Pi_mat`` -- reliability matrix.
        - ``k`` -- code dimension
        - ``L`` -- max list size

        OUTPUT:
        - ``M`` -- multiplicity matrix. [ (i, j)-th entry of this matrix can be thought of as a weight for the i-th
        field element. This weight is high if the probability that the j-th transmitted symbol equals the i-th field
        element (given the received sequence y), is high. ]

    """
    Pi_mat_copy = copy.deepcopy(Pi_mat)
    Pi_star = Pi_mat_copy

    q, n = Pi_mat_copy.dimensions()
    M = matrix(q, n, 0)  # hopefully this is all zeros

    # Create a max-heap for elements in Pi_star
    heap = []
    for i in range(q):
        for j in range(n):
            heapq.heappush(heap, (-Pi_star[i, j], i, j))  # Push negative to simulate max-heap

    while True:
        # Pop the maximum element
        pi_max, imax, jmax = heapq.heappop(heap)
        pi_max = -pi_max  # Convert back to positive

        Pi_star[imax, jmax] = Pi_mat_copy[imax, jmax] / (M[imax, jmax] + 2)
        M[imax, jmax] += 1

        Cm = get_cost_multiplicity(M)
        if math.floor(max_weighted_deg(k, Cm) / (k - 1)) > L:
            M[imax, jmax] -= 1
            break

        # Push the updated element back into the heap
        heapq.heappush(heap, (-Pi_star[imax, jmax], imax, jmax))

    return M

def monomial_list(maxdeg, wy):
    r"""
    Returns a list of all non-negative integer pairs `(i,j)` such that ``i + wy
    * j <= maxdeg``.

    INPUT:
    - ``maxdeg``, ``wy`` -- integers.

    OUTPUT:
    - ``monomials`` -- a list of pairs of integers (i, j) s.t. i + wy * j <= maxdeg.

    EXAMPLES::

        sage: monomial_list(8, 3)
        [(0, 0),
         (1, 0),
         (2, 0),
         (3, 0),
         (4, 0),
         (5, 0),
         (6, 0),
         (7, 0),
         (8, 0),
         (0, 1),
         (1, 1),
         (2, 1),
         (3, 1),
         (4, 1),
         (4, 4)]
    """
    #monomials = []
    #for y in range(0, ceil(maxdeg / wy) + 1):
    #    for x in range(0, ceil(maxdeg - y * wy)):
    #        if x + wy * y <= maxdeg:
    #            monomials.append((x, y))

    monomials = [(x, y) for y in range(0, math.ceil(maxdeg / wy) + 1) for x in range(0, math.ceil(maxdeg - y * wy) + 1) if (x + wy * y) <= maxdeg]
    # changed this

    return monomials


def interpolation_matrix_given_monomials(eval_pts, q, M, monomials):
    r"""
    Returns a matrix whose nullspace is a basis for all interpolation
    polynomials, each polynomial having its coefficients laid out according to
    the given list of monomials.

    The output is an where num. of cols. is the length of ``monomials``, and num. of rows
    is the number of constraints. Its ``i``-th column will be the coefficients on the
    ``i``-th monomial in ``monomials``.

    INPUT:

    - ``eval_pts`` -- evaluation points of the RS code.
    - ``q`` -- field size.
    - ``M`` -- multiplicity matrix for the Koetter-Vardy algorithm.
    - ``monomials`` -- a list of monomials, each represented by the powers as an integer pair `(i,j)`.
    """
    n = len(eval_pts)
    F = GF(q)

    tuples = [(eval_pts[j], F(i), M[i, j]) for j in range(n) for i in range(q) if M[i, j] > 0]

    def eqs_affine(x0, y0, r):
        r"""
        Make equation for the affine point x0, y0 with multiplicity r. Return a list of
        equations, each equation being a list of coefficients corresponding to
        the monomials in ``monomials``. Pg. 248, Essential coding theory
        """
        eqs = []

        for i in range(0, r):
            for j in range(0, r - i):
                eq = {}  # eq = dict()
                for monomial in monomials:
                    i_p = monomial[0]
                    j_p = monomial[1]
                    if i_p >= i and j_p >= j:
                        icoeff = math.comb(i_p, i) * (x0 ** (i_p - i)) \
                            if i_p > i else F(1)
                        jcoeff = math.comb(j_p, j) * (y0 ** (j_p - j)) \
                            if j_p > j else F(1)
                        #print(type(icoeff), " ", type(jcoeff))
                        assert type(icoeff) == type(jcoeff), "well"
                        eq[(i_p, j_p)] = jcoeff * icoeff  # eq[monomial] = jcoeff * icoeff
                eqs.append([eq.get(monomial, 0) for monomial in monomials])
        return eqs

    # --------------------------------------------------------------------------------------
    list_eq = matrix([eq for tt in tuples for eq in eqs_affine(tt[0], tt[1], tt[2])])

    return list_eq
    #return matrix(list(flatten_once([eqs_affine(tt[0], tt[1], tt[2]) for tt in tuples])))
    # return matrix(list(_flatten_once([eqs_affine(*point) for point in points])))


def max_weighted_deg(k, Cm):
    """Return the minimal (1, k-1)-weighted degree needed for an interpolation
    polynomial over `n` points, and the corresponding monomials, for the multiplicity matrix `M`

    INPUTS:
    - ``k`` -- code dimension.
    - ``Cm`` -- cost of multiplicity matrix for the Koetter-Vardy algorithm.

    OUTPUT:
    - ``delta`` -- max degree of bivariate polynomial
    """

    # determine max degree delta
    delta = 1

    # number of monomials (given delta & k) given by Lemma 1, Koetter-Vardy TIT
    num_monomials = (delta + 1) ** 2 / (2 * (k - 1)) + ((k - 1) / 2) * (math.ceil((delta + 1) / (k - 1)) - (math.ceil((delta + 1) / (k - 1)) - (delta + 1) / (k - 1)) ** 2)

    # This loop ensures that # monomials > # linear constraints (Equation (10), KV TIT)
    while num_monomials <= Cm:
        delta += 1
        num_monomials = (delta + 1) ** 2 / (2 * (k - 1)) + ((k - 1) / 2) * (math.ceil((delta + 1) / (k - 1)) - (math.ceil((delta + 1) / (k - 1)) - (delta + 1) / (k - 1)) ** 2)

    return delta



def interpolation_matrix_problem(eval_pts, q, k, M):
    r"""
    Returns the linear system of equations which ``Q`` should be a solution to.

    This linear system is returned as a matrix ``mat_interp`` and a list of monomials ``monomials``,
    where a vector in the right nullspace of ``mat_interp`` corresponds to an
    interpolation polynomial `Q`, by mapping the `t`'th element of such a vector
    to the coefficient to `x^iy^j`, where `(i,j)` is the `t`'th element of ``monomials``.

    INPUTS:
    - ``eval_pts`` -- evaluation points of the RS code.
    - ``q`` -- field size.
    - ``k`` -- code dimension.
    - ``M`` -- multiplicity matrix.

    OUTPUTS:
    - ``mat_interp`` -- interpolation matrix.
    - ``monomials`` -- list of monomials `x^iy^j.
    """

    Cm = get_cost_multiplicity(M)
    delta = max_weighted_deg(k, Cm)
    monomials = monomial_list(delta, k - 1)

    assert len(monomials) > Cm, "Num of monomials should be greater than cost of multiplicity matrix"

    mat_interp = interpolation_matrix_given_monomials(eval_pts, q, M, monomials) # TODO if anything needs to be checked, it's this one. But I think you did at some point.
    return mat_interp, monomials


def soft_interpolate(eval_pts, q, k, M):
    r"""
    Returns the linear system of equations which ``Q`` should be a solution to.

    This linear system is returned as a matrix ``M`` and a list of monomials ``monomials``,
    where a vector in the right nullspace of ``M`` corresponds to an
    interpolation polynomial `Q`, by mapping the `t`'th element of such a vector
    to the coefficient to `x^iy^j`, where `(i,j)` is the `t`'th element of ``monomials``.

    INPUTS:
    - ``eval_pts`` -- evaluation points.
    - ``q`` -- field size.
    - ``k`` -- an integer, the number of errors one wants to decode.
    - ``M`` -- multiplicity matrix.

    OUTPUT:
    - ``Q_list`` -- list of interpolation polynomials (each must be factorized).
    """

    ## SETUP INTERPOLATION PROBLEM
    Mat, monomials = interpolation_matrix_problem(eval_pts, q, k, M)
    PF = Mat.base_ring()['x', 'y']  # make that ring a ring in <x>
    x, y = PF.gens()
    GF_q = GF(q)

    Ker = Mat.right_kernel()

    sol_list = Ker.basis()
    Q_list = []

    # Pick a non-zero element from the right kernel
    for sol in sol_list:
        # Construct the Q polynomial
        Q = sum([(x ** monomials[i][0]) * (y ** monomials[i][1]) * GF_q(sol[i]) for i in range(len(monomials))])
        Q_list.append(Q)

    return Q_list




def encode_polynomial(C, msg_x, k, q):
    r"""
        Returns codeword in C corresponding to message polynomial.

        INPUT:
        - ``C`` -- RS code.
        - ``msg_x`` -- message polynomial.
        - ``k`` -- dimension of RS code.
        - ``q`` -- field size.

        OUTPUT:
        - ``codeword`` -- codeword.
    """
    # Ensure the polynomial coefficients are in the correct finite field
    coeffs = msg_x.coefficients(sparse=False)

    # Convert coefficients to a vector of the required length
    if len(coeffs) > k:
        raise ValueError("Polynomial degree exceeds the code length")

    vector_to_encode = vector(GF(q), coeffs + [0] * (k - len(coeffs)))

    # Encode the vector using the Reed-Solomon code
    codeword = C.encode(vector_to_encode)

    return codeword

def kv_decode(received_list, C, eval_pts, q, k, M):
    r"""
        Performs KV decoding, outputs information vector, message vector & 1/0 to indicate decoding success.

        INPUT:
        - ``received_list`` -- list of received vectors
        - ``C`` -- RS code.
        - ``eval_pts`` -- evaluation points.
        - ``k`` -- dimension of RS code.
        - ``q`` -- field size.
        - ``M`` -- multiplicity matrix
        - ``tau_id`` -- max insdels that can be corrected by given code

        OUTPUT:
        - ``est_msg_list`` -- list of decoded informatio vectors
        - ``est_codewords`` -- list of decoded codewords
        - ``success`` -- 1 if non-empty output, 0 else.
    """
    n = len(eval_pts)
    Q_list = soft_interpolate(eval_pts, q, k, M)

    tau_h = johnson_radius(n, n - k + 1)
    tau_id = n - 2*k +1
    est_msg_list = []
    est_codewords = []

    for Q in Q_list:

        polynomials = roth_ruckenstein_root_finder(Q, maxd = k - 1)  # alekhnovich_root_finder(Q, maxd = k - 1)

        # for each factor of Q(X,Y)
        for f in polynomials:
            if f.degree() >= k:
                continue

            coeffs = f.coefficients(sparse=False)

            u_est = vector(GF(q), coeffs + [0] * (k - len(coeffs)))

            if u_est in est_msg_list:
                continue

            c_est = C.encode(u_est)

            if len(est_msg_list) == 0 or all((len(received) != len(c_est) and levenshteinIterative(received,      c_est) <= tau_id) or (len(received) == len(c_est) and (received - c_est).hamming_weight() <= tau_h)
                   for received in received_list):
                est_msg_list.append(u_est)
                est_codewords.append(c_est)

    success = 0
    if len(est_msg_list) > 0:
        success = 1

    return est_msg_list, est_codewords, success


def kv_decode_rev(received_rev_list, eval_pts_rev, q, k, M_rev):
    r"""
        Performs KV decoding, outputs information vector, message vector & 1/0 to indicate decoding success.

        INPUT:
        - ``received_rev_list`` -- list of received vectors
        - ``eval_pts_rev`` -- evaluation points.
        - ``k`` -- dimension of RS code.
        - ``q`` -- field size.
        - ``M`` -- multiplicity matrix

        OUTPUT:
        - ``est_msg_list`` -- list of decoded informatio vectors
        - ``est_codewords`` -- list of decoded codewords
        - ``success`` -- 1 if non-empty output, 0 else.
    """
    n = len(eval_pts_rev)
    C_rev = codes.GeneralizedReedSolomonCode(eval_pts_rev, k)
    Q_list = soft_interpolate(eval_pts_rev, q, k, M_rev)

    est_msg_list = []
    est_codewords = []

    tau_id = n - 2*k + 1
    tau_h = johnson_radius(n, n - k + 1)

    for Q in Q_list:

        polynomials = roth_ruckenstein_root_finder(Q, maxd = k - 1) # alekhnovich_root_finder(Q, maxd = k - 1)

        # for each factor of Q(X,Y)
        for f in polynomials:
            if f.degree() >= k:
                continue

            coeffs = f.coefficients(sparse=False)

            u_est = vector(GF(q), coeffs + [0] * (k - len(coeffs)))

            if u_est in est_msg_list:
                continue

            c_est = C_rev.encode(u_est)

            #if (len(received_rev) != len(c_est) and levenshteinIterative(received_rev, c_est) <= tau1) or (len(received_rev) == len(c_est) and (received_rev - c_est).hamming_weight() <= tau):
            if all((len(received) != len(c_est) and levenshteinIterative(received, c_est) <= tau_id) or
                   (len(received) == len(c_est) and (received - c_est).hamming_weight() <= tau_h)
                   for received in received_rev_list):
                est_msg_list.append(u_est)
                est_codewords.append(c_est[::-1])

    success = 0
    if len(est_msg_list) > 0:
        success = 1

    return est_msg_list, est_codewords, success
