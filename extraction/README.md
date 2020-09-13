# Extraction

Contains two implementations:

* Pretty-printing procedure from the deep embedding into the Liquidity syntax. Smart contracts have to be written in ``λsmart`` using the notations.

* Extraction using MetaCoq's certified erasure. Extracts smart contracts implemented in Gallina. Can handle some form of dependent types. Currently supports Liquidity and Midlang (Elm) as a target language.
