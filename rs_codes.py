import numpy as np
from sage.all import *
import auxiliary, itertools, math
import random as rm
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
def johnson_radius(n, d):
    r"""
    Returns the Johnson-radius for the code length `n` and the minimum distance `d`.

    The Johnson radius is defined as `n - \sqrt(n(n-d))`.

    INPUT:

    - ``n`` -- an integer, the length of the code
    - ``d`` -- an integer, the minimum distance of the code

    EXAMPLES::

        sage: sage.coding.guruswami_sudan.utils.johnson_radius(250, 181)
        -5*sqrt(690) + 250
    """
    return n - math.sqrt(n * (n - d))


def getRScode(n,k,q):
    GF_q = GF(q)
    eval_pts = random.sample(GF_q.list(), n) #GF_q.list()[:n]
    C = codes.GeneralizedReedSolomonCode(eval_pts, k)  # eval points, dimension
    code_param = auxiliary.CodeParams(q, n, k, eval_pts)

    return C, code_param

def compute_score(cl, mult_matrix):
    sc = 0

    for i in range(len(cl)):
        sc = sc + mult_matrix[cl[i], i]

    return sc


def check_alg_sufficiency(q, n, k, eval_pts, t):
    r"""
        Checks if a given RS code can correct t insdel errors.

        INPUT:

        - ``q`` -- field size
        - ``n`` -- length of RS code
        - ``k`` -- dimension of RS code
        - ''eval_pts'' -- eval pts of RS code
        - ``t`` -- number of insdels guaranteed to be corrected

    """
    # for every 2 inc. vectors of length 2k-1 from [1....n], the Vandermonde-like matrix should be of full rank
    Fq = GF(q)
    powers = np.array([[e ** j for e in eval_pts] for j in range(1, k)], dtype=object)

    vand_matrix = matrix(Fq, n - t, 2 * k - 1)      # initialize vandermonde matrix
    for i in range(n - t):
        vand_matrix[i, 0] = 1

    # step 1: initialize matrix of n choose n - t increasing vectors
    inc_vec_matrix = list(itertools.combinations(list(range(0, n)), n - t)) # Generate all possible strictly increasing sequences of length n - t
    rm.shuffle(inc_vec_matrix)
    # step 2, iterate through all distinct I, J from this matrix. I,J agree on at most k-1 coordinates

    for i in range(len(inc_vec_matrix)):
        seq_1 = inc_vec_matrix[i]
        #I_eval = [eval_pts[idx] for idx in seq_1]

        # fill up first part of vand_matrix
        for b in range(1, k):
            for a in range(n-t):
                vand_matrix[a, b] = powers[b - 1][seq_1[a]] #I_eval[a] ** b

        for j in range(i + 1, len(inc_vec_matrix)):
            seq_2 = inc_vec_matrix[j]

            # seq_1 & seq_2 must agree on at most k - 1 coordinates
            if sum(1 for x, y in zip(seq_1, seq_2) if x == y) > k - 1: # changed k to k - 1
                continue

            #print("I: ", I_eval)
            #print("J: ", J_eval)
            #print("#agreeing positions: ", sum(1 for x, y in zip(seq_1, seq_2) if x == y))

            # fill up 2nd part of vand_matrix
            for a in range(n - t):
                for b in range(1, k):
                    vand_matrix[a, b + k - 1] = powers[b - 1][seq_2[a]] #J_eval[a] ** b

            # step 3: build vandermonde-like matrix, check if full rank. if not return false.
            if vand_matrix.rank() != (2 * k - 1):
                return False
    """
    for i, seq_1 in enumerate(inc_vec_matrix):
        for b in range(1, k):
            vand_matrix[:, b] = vector(Fq, [powers[b - 1][idx] for idx in seq_1])

        for j in range(i + 1, len(inc_vec_matrix)):
            seq_2 = inc_vec_matrix[j]

            # Early exit for sequence agreement check
            if sum(1 for x, y in zip(seq_1, seq_2) if x == y) > k - 1:  # changed k to k - 1
                continue

            # Update matrix with second sequence's powers
            for b in range(1, k):
                vand_matrix[:, b + k - 1] = vector(Fq, [powers[b - 1][idx] for idx in seq_2])

            # Rank check
            if vand_matrix.rank() != 2 * k - 1:
                return False
    """
    return True


def check_pair(seq_1, seq_2, k, n_t, powers, eval_pts, q):
    """Check a single pair of sequences for the rank condition."""
    if sum(1 for x, y in zip(seq_1, seq_2) if x == y) > k - 1:
        return True  # Skip this pair if they agree on more than k-1 coordinates.

    Fq = GF(q)
    vand_matrix = matrix(Fq, n_t, 2 * k - 1)

    for i in range(n_t):
        vand_matrix[i, 0] = 1

    # Fill the first part of vand_matrix with seq_1
    for b in range(1, k):
        for a in range(n_t):
            vand_matrix[a, b] = powers[b - 1][seq_1[a]]

    # Fill the second part of vand_matrix with seq_2
    for a in range(n_t):
        for b in range(1, k):
            vand_matrix[a, b + k - 1] = powers[b - 1][seq_2[a]]

    # Check if the matrix is full rank
    return vand_matrix.rank() == (2 * k - 1)


def check_alg_sufficiency2(q, n, k, eval_pts, t):
    r"""
    Checks if a given RS code can correct t insdel errors.
    """
    Fq = GF(q)
    powers = np.array([[e ** j for e in eval_pts] for j in range(1, k)], dtype=object)

    # Generate all increasing vectors of length n - t
    inc_vec_matrix = list(itertools.combinations(range(n), n - t))
    rm.shuffle(inc_vec_matrix)

    n_t = n - t

    """
    # all pairs of indices of increasing vectors to be examined
    pairs = [(inc_vec_matrix[i], inc_vec_matrix[j])
             for i in range(len(inc_vec_matrix))
             for j in range(i + 1, len(inc_vec_matrix))]

    with ProcessPoolExecutor() as executor:
        futures = {executor.submit(check_pair, seq_1, seq_2, k, n_t, powers, eval_pts, q): (seq_1, seq_2)
                   for seq_1, seq_2 in pairs}

        for future in as_completed(futures):
            if not future.result():  # If any pair fails, return False
                return False
    """

    # Generator for pairs of indices
    def pair_generator():
        for i in range(len(inc_vec_matrix)):
            for j in range(i + 1, len(inc_vec_matrix)):
                yield inc_vec_matrix[i], inc_vec_matrix[j]

    with ProcessPoolExecutor() as executor:
        # Submit tasks lazily using the generator
        futures = {executor.submit(check_pair, seq_1, seq_2, k, n_t, powers, eval_pts, q): (seq_1, seq_2)
                   for seq_1, seq_2 in pair_generator()}

        for future in as_completed(futures):
            if not future.result():  # If any pair fails, return False
                return False

    return True


def get_score_thresh(delta, k):
    r"""
        Computes number of monomials of (1, k-1)-degree at most delta.
        (Equation 2, Algebraic Soft-Decision Decoding of Reed–Solomon Codes)
    """
    return (delta + 1) ** 2 / (2 * (k - 1)) + ((k - 1) / 2) * (math.ceil((delta + 1) / (k - 1)) - (math.ceil((delta + 1) / (k - 1)) - (delta + 1) / (k - 1)) ** 2)

def get_delta(k, nu):
    r"""
        Outputs the degree delta, which ensures that number of monomials with (1,k-1)-degree at most delta, exceeds the
        number of linear constraints given by the multiplicity matrix

        INPUT:
            - ``nu``-- number of linear constraints we get from the multiplicity matrix
            - ``k`` -- dimension of RS code
    """
    i_start = 1

    while get_score_thresh(i_start, k) <= nu:
        i_start += 1

    return i_start
