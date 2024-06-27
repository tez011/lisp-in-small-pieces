# lisp in small pieces

This repository contains code I wrote while implementing software described in [Lisp in small pieces](https://christian.queinnec.org/WWW/LiSP.html).

I run these source files in [DrRacket](https://racket-lang.org/) using the R5RS language, which is not far removed from the R4RS used by Queinnec.

### Chapter 3
The continuation of a block is all the things that happen after it. That includes the next iteration of the infinite loop, dinner, and a bath before bedtime. The continuation can be intercepted with something like `call/cc` so that work is done before the continuation is called, or even in place of it (in the case of an exceptional condition).

### Chapter 4
To separate the concepts of assignment and data mutation, we allow an *environment* to map names to addresses, and a *memory store* to map addresses to values (i.e. the contents of memory at the address). 

### Chapter 5
The concept of a continuation didn't really click until I got here.
