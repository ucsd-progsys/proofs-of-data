# Proofs of Data

Verified functional data structures with LiquidHaskell. 

Inspired by Andrew Appel's [Verified Functional Algorithms][vfa].

## Chapter dependencies

```
- Perm  -> Sort  -> Selection  -> SearchTree -> Redblack
  |        |                      |
  `->Trie  `-> Multiset           `-> ADT -> Priqueue -> Binom
```

## Issues

- RedBlack hammers PLE-SLOW

## Progress

- [x] Perm
- [x] Sort
- [x] Multiset
- [x] Selection
- [x] TotalMaps
- [x] SearchTree
- [x] Trie
- [-] ADT
- [x] Priqueue
- [ ] Binom       <--------------------------- HEREHEREHEREHEREHEREHERE
- [x] RedBlack

[vfa]: https://softwarefoundations.cis.upenn.edu/vfa-current/index.html 
