LH = liquid -i src 

top: 
	$(LH) src/Trie.hs

all:
	liquid ProofCombinators.hs
	liquid Lists.hs
	liquid Perm.hs
	liquid Sort.hs
	liquid Selection.hs
	liquid TotalMaps.hs
	liquid SearchTree.hs

clean:
	rm -rf src/*.hi src/*.o
