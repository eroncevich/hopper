[![Build Status](https://travis-ci.org/cuplv/hopper.svg?branch=master)](https://travis-ci.org/cuplv/hopper)

Hopper
======

Hopper is a goal-directed static analysis tool for languages that run on the JVM. It is a much-improved and more feature-ful version of [Thresher](https://github.com/cuplv/thresher) written in Scala rather than Java.

This is an extended version of Hopper, adding in dependency analysis for Framework Relevant Slicing

Installation
------------
Hopper requires [sbt](http://www.scala-sbt.org/download.html) 0.1 or later.

(1) Download [Droidel](https://github.com/cuplv/droidel) and follow its installation instructions. Publish Droidel to your local Maven repository by running `sbt publishLocal` in the droidel/ directory.

(2) Download [Z3](https://github.com/Z3Prover/z3), compile the Java bindings, and copy the produced *.dylib (OSX), *.so (Linux), and *.jar files to hopper/lib:

```
mkdir lib; cd lib
git clone https://github.com/Z3Prover/z3.git; cd z3
python scripts/mk_make.py --java; cd build
make
cp *.jar ../..
cp *.dylib ../.. || cp *.so ../..
cd ../..
```

(3) In order to use the Android clients or compile/run the tests, you'll need a Droidel-processed Android framework JAR in lib/: `cp ../droidel/stubs/out/droidel_android-4.4.2_r1.jar lib` (assuming `droidel` and `hopper` are sibling directories).

(4) Build Hopper with `sbt one-jar` and run with `./hopper.sh`.

Usage
-----
Run 

    ./hopper.sh <path_to_bytecodes> <path_to_file_containing_sensitive_method>

where `<path_to_bytecodes>` is a path to a JAR or directory containing the Java bytecodes to be checked and `<path_to_file_containing_sensitive_method>` is a file containing the desired sensitive method. An example of this is running `./hopper.sh testExamples/Unit1.1/ testExamples/SenUnit1` which will attempt to find the path to SenUnit1 in the Unit1.1 example.

Tests
-----
A number of unit tests can be found in `./testExamples` along the file containing the sensitive method.

About
-----
The core functionality of Hopper is an engine for *refuting* queries written in separation logic; that is, showing that no concrete execution can satisfy the query. Hopper performs a form of proof by contradiction: it starts from a query representing a bad program state (such as a null dereference or out-of-bounds array access) and works backward in an attempt to derive **false**. 

Hopper has several built-in clients (as described above) but writing your own clients is meant to be easy: just extend the `Client` class and write a checker that takes a program as input and emits separation logic formulae representing your client.

This extension of hopper allows for framework relevance slicing of programs.

For more on Hopper and its predecessor tool Thresher, see our OOPSLA '15 [paper](http://www.cs.colorado.edu/~bec/papers/controlfeasibility-oopsla15.pdf), our PLDI '13 [paper](http://www.cs.colorado.edu/~bec/papers/thresher-pldi13.pdf) or the Thresher [project page](http://pl.cs.colorado.edu/projects/thresher/).

Bugs found
----------
Here is a selection of bugs found using the assistance of Hopper/Thresher:

[Android framework](https://code.google.com/p/android/issues/detail?id=48055) - write into all HashMap's (fixed)

[SeriesGuide Android app](https://github.com/UweTrottmann/SeriesGuide/pull/449) - null dereference (fixed)

[SeriesGuide Android app](https://github.com/UweTrottmann/SeriesGuide/pull/450) - null dereference (fixed)

[ConnectBot Android app](https://github.com/connectbot/connectbot/pull/60) - null dereference (fixed)

[ConnectBot Android app](https://github.com/connectbot/connectbot/pull/61) - null dereference (fixed)

[LastFM Android app](https://github.com/lastfm/lastfm-android/pull/5) - null dereference

[K9Mail Android app](https://groups.google.com/forum/?fromgroups=#!topic/k-9-mail/JhoXL2c4UfU) - memory leak (fixed)

[Jython](https://bitbucket.org/jython/jython/pull-request/52/fixing-potential-array-index-out-of-bounds) - array out of bounds error

Troubleshooting
---------------
Problem: Hopper compilation fails with missing dependency from `walautil` or `droidel`.
Solution: Your `walautil` and `droidel` projects might be out of date. Try `git pull; sbt publishLocal` in each directory.

Problem: Hopper fails at runtime with a message like: `java.lang.NoSuchMethodError: scala.collection.immutable.$colon$colon.hd$1()Ljava/lang/Object;`.
Solution: This happens when Hopper is run with the wrong version of Scala; make sure you are using Scala 2.10.

Problem: Hopper fails at runtime with a message like: `java.lang.UnsupportedClassVersionError: edu/colorado/walautil/cg/ImprovedZeroXContainerCFABuilder : Unsupported major.minor version 52.0`.
Solution: This happens when Hopper and `walautil` are built using different JDK versions. You may need to rebuild `walautil` and `sbt publishLocal` again.
