---
layout: page
title: Resources
permalink: /resources/
---

# Course Website

This course website, including all of the lecture materials, lives
[here](http://kcsrk.info/cs6225_s20_iitm/).

# Software

## Coq

For Coq, I use [CoqIDE](https://github.com/coq/coq/releases/tag/V8.10.2).
If you are an emacs user, then [Proof General](https://proofgeneral.github.io/)
is recommended.

You will need to ensure that the location of the Coq binaries is in your `PATH`
so that the make files for the frap book and the assignments work. On MacOS,
this means that the following line is included in my `.bashrc` file:

```bash
export PATH=$PATH:/Applications/CoqIDE_8.10.2.app/Contents/Resources/bin/
```

This will vary between OS versions. We will ensure that everyone has a working
environment by the end of first week.

## F\*

The easiest way to try out F\* quickly is directly in your browser using the
[online editor that's part of the F\*
tutorial](https://www.fstar-lang.org/run.php). There is also a better,
experimental [online editor](http://fstar.ht.vc/).

I use [Spacemacs](https://www.spacemacs.org/) +
[Fstar-mode.el](https://github.com/FStarLang/fstar-mode.el) + [Spacemacs layer
for F\*](https://github.com/kyoDralliam/fstar-layer/). I recommend this setup
for interactive development. 

# Text Books

We will be closely following 

* *Formal Reasoning about Programs*, Adam Chlipala. Freely available
  [online](http://adam.chlipala.net/frap/).

for the Coq part of the course. For F\*, there is no prescribed text book. We
will look at examples from the [tutorials](https://www.fstar-lang.org/tutorial/)
and [other](https://prosecco.gforge.inria.fr/personal/hritcu/teaching/vtsa2019/)
[lectures](https://www.cs.uoregon.edu/research/summerschool/summer19/topics.php#Swamy).

Other reference books are:

* *Software Foundations*, Benjamin Pierce et al. Freely available [online](https://softwarefoundations.cis.upenn.edu/).
* *Types and Programming Languages*, Benjamin Pierce, MIT Press, 1st edition,
  2002. Ebook is available in IITM library.
* *Practical Foundations for Programming Languages*, Robert Harper, Cambridge
  University Press, 2nd edition, 2016. Freely available [online](https://www.cs.cmu.edu/~rwh/pfpl/2nded.pdf).

# Tactics Reference

* Appendix in the [Frap book](http://adam.chlipala.net/frap/frap_book.pdf)
* [Cornell CS3110 Coq Cheat Sheet](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html#leftright)
* [Coq tactic index](https://pjreddie.com/coq-tactics/)
* [Coq manual](https://coq.inria.fr/refman/proof-engine/tactics.html)
