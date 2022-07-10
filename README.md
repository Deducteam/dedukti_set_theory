# Implementation of Set Theory in Dedukti

This repository presents the code of an **implementation of set theory in Dedukti** [2]. The version of set theory implemented is Dowek-Miquel’s intuitionistic set theory [1], in which sets are represented by a primitive notion of pointed graphs. To achieve this implementation, we have defined a peculiar class of formulas along with its interpretation in the theory. 

The repository is composed of several code files, organized as follows and where the numbering of lemmas corresponds to the one in [1]:

- `logic.lp` contains the basis of **logic**

- `nat.lp` contains the definition of **natural numbers**

- `language.lp` contains the defintion of the theory of **pointed graphs**

- `formulas.lp` contains the development of the **type of formulas**

- `language2.lp` contains an **extension of the language** using formulas

- `bisimilarity.lp` contains **lemmas 3 to 6**

- `injectivity.lp` contains **lemmas 7 to 13**

- `eta1.lp` contains **lemmas 14 to 18**

- `eta2.lp` contains **lemmas 19 to 21**

- `eta3.lp` contains **lemmas 22 to 27**

- `membership.lp` contains **lemmas 28 to 31**

- `formulas_lemmas.lp` contains **intermediate lemmas** that use formulas

- `lemma32.lp` contains **lemma 32**

- `relocation.lp` contains **lemmas 33 and 34**

- `embedding.lp` contains **lemmas 35 to 40**

- `lemma41.lp` contains **lemma 41**

- `weak_extensionality.lp` contains the proofs of **weak extensionality**

- `finitary.lp` contains **lemmas 42 to 45**

- `infinity.lp` contains **lemmas 46 to 51**

- `closure.lp` contains **lemmas 52 and 53**.


# References

[1] G. Dowek & A. Miquel, "Cut elimination for Zermelo set theory". Manuscript available on the website of the authors, http://www.lsv.fr/~dowek/Publi/zermodulo.pdf, 2007.

[2] V. Blot, G. Dowek & T. Traversié, "An Implementation of Set Theory with Pointed Graphs in Dedukti". Not yet available, 2022.
