<h1>Map2Check</h1>
<h2>Finding Software Vulnerabilities using Symbolic Execution and Fuzzing</h3>

<link rel="stylesheet" href="https://use.fontawesome.com/releases/v5.6.1/css/all.css" integrity="sha384-gfdkjb5BdAXd+lj+gudLWI+BXq4IuLW5IT+brZEZsLFm++aCMlF1V92rMkPaX4PP" crossorigin="anonymous">

[![Build Status](https://travis-ci.org/hbgit/Map2Check.svg?branch=develop)](https://travis-ci.org/hbgit/Map2Check)

___

<p align="justify">
<b>Map2Check</b> is a bug hunting tool that automatically generating and checking safety properties in C programs.
It tracks memory pointers and variable assignments to check user-specified assertions, overflow, and pointer safety.
The generation of the tests cases are based on assertions (safety properties) from the code instructions, adopting the
[LLVM framework](http://llvm.org/) version 6.0, [LibFuzzer](https://llvm.org/docs/LibFuzzer.html) [KLEE](https://klee.github.io/) to generate input values to the test cases generated by Map2Check. Additionally, we have adopted [Crab-LLVM] (https://github.com/seahorn/crab-llvm) tool to computes inductive invariants for LLVM-based languages.
</p>

Extra documentation is available at https://map2check.github.io

___

#### Requirements for using the tool

To use the Map2Check tool is necessary a Linux 64-bit OS system. In the linux OS, you should install the  requirements, typing the commands:
``` bash
$ sudo apt install python-minimal
$ sudo apt install libc6-dev
```

Our binary tool is avaliable at https://github.com/hbgit/Map2Check/releases

#### Install Map2Check

<p align="justify">
In order to install Map2Check on your PC, you should download and save the map2check zip file on your disk from https://github.com/hbgit/Map2Check/releases.
After that, you should type the following command:
</p>

``` bash
$ unzip map2check-rc-v7.3-svcomp20.zip
$ cd map2check-rc-v7.3-svcomp20
```

#### Running the tool

<p align="justify">
Map2Check can be invoked through a standard command-line interface. Map2Check should be called
in the installation directory as follows:  
</p>

``` bash
$ ./map2check --memtrack svcomp_960521-1_false-valid-free.c
```

In this case, --memtrack is the option to check for memory errors. For help and others tool options:

``` bash
$ ./map2check --help
```

When you use a LLVM bytecode as input for the tool, be sure to add `-g` flag when generating the file, it is not required, but map2check will provide better info (like line numbers).

___

#### How to build Map2Check?

<p align="justify">
You can build Map2Check using our [Dockerfile](./Dockerfile) by clone our repository:
</p>

``` bash
$ git clone https://github.com/hbgit/Map2Check.git
$ cd Map2Check
$ git submodule update --init --recursive
# Build docker image to compile Map2Check
$ docker build -t hrocha/mapdevel --no-cache -f Dockerfile .
$ docker run --rm -v $(pwd):/home/map2check/devel_tool/mygitclone:Z --user $(id -u):$(id -g) hrocha/mapdevel /bin/bash -c "cd /home/map2check/devel_tool/mygitclone; ./make-release.sh; ./make-unit-test.sh"
```

More details at https://map2check.github.io/docker.html

#### How to run the regression testing

<p align="justify">
You should build the [Benchexec](https://github.com/sosy-lab/benchexec) docker image that is available in our repository in the submodule (utils/benchexecrun):
</p>

``` bash
$ cd Map2Check
$ docker build -t hrocha/benchexecrun --no-cache -f utils/benchexecrun/Dockerfile utils/benchexecrun/
# Running the regression testing
$ ./make-regression-test.sh t
```

___

#### Instructions for SV-COMP'20

Use the ['map2check-wrapper.py'](utils/map2check-wrapper.py) script in the Map2Check binary directory to verify each single test-case.

Usage:

``` bash
$ ./map2check-wrapper.py -p propertyFile.prp file.i
```

<p align="justify">
Map2Check accepts the property file and the verification task and provides as verification result:
<b>TRUE + Witness</b>, <b>[FALSE|FALSE(p)] + Witness</b>, or <b>UNKNOWN</b>.
FALSE(p), with p in {valid-free, valid-deref, valid-memtrack, valid-memcleanup}, means that the (partial)
property p is violated.
For each verification result the witness file (called <b>witness.graphml</b>) is generated Map2Check root-path folder.
There is timeout of 897 seconds set by this script, using "timeout" tool that is part of coreutils
on debian. If these constraints are violated, it should be treated as UNKNOWN result.
</p>

___

#### Authors

Maintainers:
  - Herbert O. Rocha (since 2014), Federal University of Roraima, Brazil - https://hbgit.github.io/
  - Rafael Menezes   (since 2016), Federal University of Roraima, Brazil - https://rafaelsa94.github.io/

Questions and bug reports:  
  E-mail: map2check.tool@gmail.com

          .-.          
          /v\
         // \\    > L I N U X - GPL <
        /(   )\
         ^^-^^
