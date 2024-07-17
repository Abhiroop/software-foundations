# Software Foundations

Working through all of the exercises in the classic series - Software Foundations - https://softwarefoundations.cis.upenn.edu/

Currently on Vol 1.

### Adding new files
```
make clean
-- create new_file.v and add the required export
coq_makefile -f _CoqProject *.v -o Makefile
make
```
