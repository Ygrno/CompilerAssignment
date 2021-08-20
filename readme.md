# Compiler FROM Scheme to Assembly64

This compiler was created as part of a University Project.

## About 

The compiler conssists of 4 Modules:

### Reader -> Tag-Parser -> Semantic-Analyser -> Code-Gen

Each module has a unique part in the process of converting a code written in scheme to Assembly.
The user shall provide the compiler with a file containing a string that represents a scheme code. 
The string would be scanned, tagged, improved and finally will be converted to fully working Assembly code.

The compiler does not support all the features of scheme language, *but* it certainly helps to understand how the compiling process works.

## Prerequisites
The project was tested on linux machines with make, ocaml and nasm installed.

## Authors
* **Rotem Dayan** 
* **Yakir Green**




