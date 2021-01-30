# CS6225 : Programs and Proofs

This is the website for the Spring 2021 course "Programs and Proofs" at the
Department of Computer Science and Engineering at the Indian Institute of
Technology, Madras.

## Coq sources

The lecture materials are available in `lectures/`. In order to step through the
lectures in CoqIDE, you will first need to build the Frap library in `frap/`. To
build, ensure that you have a Coq distribution installed. If you are using
CoqIDE ensure that there aren't two different distributions of Coq installed on
your machine. Easiest is to install the CoqIDE and then add the `bin` directory
from the distribution to your `PATH`. On MacOS, this means that the following
line is included in my `.bashrc` file:

```bash
export PATH=$PATH:/Applications/CoqIDE_8.10.2.app/Contents/Resources/bin/
```

Now the frap library can be built by:

```bash
$ cd frap
$ make
```

Then you can open the `*.v` files in CoqIDE and step through. 
