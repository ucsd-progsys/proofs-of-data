# Proofs of Data

A port of Andrew Appel's [Verified Functional Algorithms](https://softwarefoundations.cis.upenn.edu/vfa-current/index.html) to LiquidHaskell


## Chapter dependencies

```
- Perm  -> Sort  -> Selection  -> SearchTree -> Redblack
  |        |                      |
  `->Trie  `-> Multiset           `-> ADT -> Priqueue -> Binom
```

## Progress

- [x] Perm
- [x] Sort
- [x] Multiset
- [x] Selection
- [x] TotalMaps
- [x] SearchTree
- [x] Trie
- [-] ADT
- [ ] Priqueue
- [ ] Binom
- [x] RedBlack      <------ PLE-SLOW

## Sizes

```
- [x] 247    1382    8914 Sort.v
- [x] 251    1232    8022 Multiset.v
- [x] 251    1267    7988 Selection.v
- [ ] 272    1459    9083 Priqueue.v
- [x] 327    1878   11330 Maps.v
- [ ] 392    2083   12687 Binom.v
- [x] 619    3199   20067 Perm.v
- [x] 693    4233   25942 Trie.v
- [x] 792    4627   26478 Redblack.v
- [x] 908    5123   31232 SearchTree.v
```
