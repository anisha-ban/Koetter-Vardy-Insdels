from sage.all import *

def transmit(in_vector, q, pI, pD, pS):
    r"""
    Transmits an input vector (in_vector) over an IDS channel. Alphabet is of size q.

    INPUT:

    - ``in_vector`` -- vector to be transmitted.
    - ``q`` -- field size.
    - ``pI`` -- insertion probability.
    - ``pD`` -- deletion probability.
    - ``pS`` -- substitution probability.

    """
    n1 = len(in_vector)
    out_vector = []
    i = 0
    GF_q = GF(q)

    ins, dels = 0, 0
    del_pos = []

    while i < n1:
        pl = random()
        if pl < pI:
            out_vector.append(GF_q.random_element())
            ins += 1
        elif pI <= pl < pI + pD:
            del_pos.append(i)
            i += 1
            dels += 1
        else:
            pl = random()
            if pl < pS:
                elements = list(GF_q)
                elements.remove(in_vector[i])
                out_vector.append(random.choice(elements))
            else:
                out_vector.append(in_vector[i])
            i = i + 1

    # Convert the output list to a vector over GF(q)
    out_vector = vector(GF_q, out_vector)
    return out_vector


def get_drift_probabilities(ylen, xlen, pI, pD):
    r"""
        Generates a matrix (real values) of size (xlen + 1) x (ylen +1).
        The (i, j)-th entry of this matrix represents the probability (logarithmic) that after the transmission of
        a vector of length (i - 1), a vector of length (j - 1) was received. This IDS channel has insertion and deletion
        probabilities pI and pD respectively.

        INPUT:

        - ``ylen`` -- total length of received vector.
        - ``xlen`` -- total length of transmitted vector / codeword.
        - ``pI`` -- insertion probability.
        - ``pD`` -- deletion probability.

        """
    pT = 1 - pI - pD

    drift_prob = Matrix(RR, xlen + 1, ylen + 1)
    drift_prob[0, 0] = 0.0

    # row 0, all insertions
    for r in range(1, ylen + 1):
        drift_prob[0, r] = drift_prob[0, r - 1] + log(pI)

    # col 0, all deletions
    for t in range(1, xlen + 1):
        drift_prob[t, 0] = drift_prob[t - 1, 0] + log(pD)

    # all rows (except last), all columns
    for t in range(1, xlen):
        for r in range(1, ylen + 1):
            drift_prob[t, r] = log(exp(drift_prob[t - 1, r - 1] + log(pT)) + exp(drift_prob[t, r - 1] + log(pI))
                                   + exp(drift_prob[t - 1, r] + log(pD)))

    # consider last row, i.e., t = xlen
    for r in range(1, ylen + 1):
        drift_prob[xlen, r] = log(exp(drift_prob[xlen - 1, r - 1] + log(pT)) + exp(drift_prob[xlen - 1, r] + log(pD)))


    return drift_prob

def get_drift_probabilities_rev(ylen, xlen, pI, pD):
    r"""
        (State diagram for transmission from reverse)
        Generates a matrix (real values) of size (xlen + 1) x (ylen +1).
        The (i, j)-th entry of this matrix represents the probability that after the transmission of a vector
        of length (i - 1), a vector of length (j - 1) was received. This IDS channel has insertion and deletion
        probabilities pI and pD respectively.

        INPUT:

        - ``ylen`` -- total length of received vector.
        - ``xlen`` -- total length of transmitted vector / codeword.
        - ``pI`` -- insertion probability.
        - ``pD`` -- deletion probability.

        """
    pT = 1 - pI - pD

    drift_prob = matrix(RR, xlen + 1, ylen + 1)
    drift_prob[0, 0] = 0.0

    # row 0, inaccessible from reverse direction
    for r in range(1, ylen + 1):
        drift_prob[0, r] = -math.inf

    # col 0, all deletions
    for t in range(1, xlen + 1):
        drift_prob[t, 0] = drift_prob[t - 1, 0] + log(pD)

    # all rows (except last), all columns
    for t in range(1, xlen + 1):
        for r in range(1, ylen + 1):
            drift_prob[t, r] = log(exp(drift_prob[t - 1, r - 1] + log(pT))
                                   + exp(drift_prob[t, r - 1] + log(pI))
                                   + exp(drift_prob[t - 1, r] + log(pD)))


    return drift_prob


def get_transmit_probabilities(q, ylen, xlen, pI, pD):
    r"""
        Generates a matrix (real values) of size (xlen + 1) x (ylen +1).
        The (i, j)-th entry of this matrix represents the probability (logarithmic) that after the transmission of
        a vector of length (i - 1), a specific vector of length (j - 1) was received. This IDS channel has insertion and deletion
        probabilities pI and pD respectively.

        INPUT:

        - ``q`` -- field size.
        - ``ylen`` -- total length of received vector.
        - ``xlen`` -- total length of transmitted vector / codeword.
        - ``pI`` -- insertion probability.
        - ``pD`` -- deletion probability.

        """
    pT = 1 - pI - pD

    tr_prob = matrix(RR, xlen + 1, ylen + 1)
    tr_prob[0, 0] = 0.0

    # horizontal, diagonal & vertical weights
    hw, dw, vw = log(pI) - log(q), log(pT) - log(q), log(pD)

    # row 0, all insertions
    for r in range(1, ylen + 1):
        tr_prob[0, r] = tr_prob[0, r - 1] + hw

    # col 0, all deletions
    for t in range(1, xlen + 1):
        tr_prob[t, 0] = tr_prob[t - 1, 0] + vw

    # all rows (except last), all columns
    for t in range(1, xlen):
        for r in range(1, ylen + 1):
            tr_prob[t, r] = log(exp(tr_prob[t - 1, r - 1] + dw) + exp(tr_prob[t, r - 1] + hw)
                                   + exp(tr_prob[t - 1, r] + vw))

    # consider last row, i.e., t = xlen
    for r in range(1, ylen + 1):
        tr_prob[xlen, r] = log(exp(tr_prob[xlen - 1, r - 1] + dw) + exp(tr_prob[xlen - 1, r] + vw))


    return tr_prob

def get_transmit_probabilities_rev(q, ylen, xlen, pI, pD):
    r"""
        (State diagram for transmission from reverse)
        Generates a matrix (real values) of size (xlen + 1) x (ylen +1).
        The (i, j)-th entry of this matrix represents the probability that after the transmission of a vector
        of length (i - 1), a specific vector of length (j - 1) was received. This IDS channel has insertion and deletion
        probabilities pI and pD respectively.

        INPUT:

        - ``q`` -- field size.
        - ``ylen`` -- total length of received vector.
        - ``xlen`` -- total length of transmitted vector / codeword.
        - ``pI`` -- insertion probability.
        - ``pD`` -- deletion probability.

        """
    pT = 1 - pI - pD

    # horizontal, diagonal & vertical weights
    hw, dw, vw = log(pI) - log(q), log(pT) - log(q), log(pD)

    tr_prob = matrix(RR, xlen + 1, ylen + 1)
    tr_prob[0, 0] = 0.0

    # row 0, inaccessible from reverse direction
    for r in range(1, ylen + 1):
        tr_prob[0, r] = -math.inf

    # col 0, all deletions
    for t in range(1, xlen + 1):
        tr_prob[t, 0] = tr_prob[t - 1, 0] + vw

    # all rows (except last), all columns
    for t in range(1, xlen + 1):
        for r in range(1, ylen + 1):
            tr_prob[t, r] = log(exp(tr_prob[t - 1, r - 1] + dw)
                                   + exp(tr_prob[t, r - 1] + hw)
                                   + exp(tr_prob[t - 1, r] + vw))

    return tr_prob
