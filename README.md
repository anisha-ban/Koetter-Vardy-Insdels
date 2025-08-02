# Koetter-Vardy algorithm for insertions & deletions

This project provides an implementation of the Koetter-Vardy decoding algorithm [3] to correct insertion & deletion errors [1] induced in codewords of an RS code during transmission over an instance of the Davey-MacKay channel[2].

SAGE version 10.3 was used.

Thanks to [Roni Con](https://ronicon.bitbucket.io/) for contributing to this project! :)

## Files

- `kv_insdel.py` -> used to run simulations (example usage explained below)
- `auxiliary.py` -> contains other helper functions
- `channel_func.py` -> contains auxiliary functions related to Davey-MacKay channel
- `rs_codes.py`-> contains auxiliary functions related to RS codes

## How to use

The Jupter Notebook `notebook.py` offers a gentle introduction to the script.

One may also run `kv_insdel.py` for simulation purposes after setting the following parameters.
- n, k: length & dimension of RS code to be used
- t: number of insertions & deletions
- M: number of received sequences
- Pi, Pd: insertion & deletion probabilities
- L: list size (parameter of the KV deocder)
- output_folder: folder where the JSON file containing FER & BER results will be saved

Example usage:

```bash
    python kv_insdel.py $n $k $t $M $Pi $Pd $L $output_folder
```

For instance, one can run:

```bash
    python kv_insdel.py 100 33 2 0.004 0.004 5 Sim
```

Number of iterations is set to `numIter=5000` in main() by default.

## References

[1] Anisha Banerjee, Roni Con, Antonia Wachter-Zeh, Eitan Yaakobi, _Decoding Insertions/Deletions via List Recovery_, 2025 IEEE International Symposium on Information Theory (ISIT)

[2] M. C. Davey and D. J. C. Mackay, "Reliable communication over channels with insertions, deletions, and substitutions," in IEEE Transactions on Information Theory, vol. 47, no. 2, pp. 687-698, Feb 2001, doi: 10.1109/18.910582.

[3] R. Koetter and A. Vardy, "Algebraic soft-decision decoding of Reed-Solomon codes," in IEEE Transactions on Information Theory, vol. 49, no. 11, pp. 2809-2825, Nov. 2003, doi: 10.1109/TIT.2003.819332
