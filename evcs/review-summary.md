Review 1:

[x] Too much assumed knowledge: higher-order effects, algebraic semantics definition, monads

[x] (see below) Link with Eelco's work is not clear

Review 2:

[~] Strong claims need to be argued or removed:
	x Hefty Algebras -> link to preprint
	- Better motivation for Hefty Algebras compared to existing language frameworks
	x ^ Eelco was looking for compilation framework that abstracts over control flow -> Reword and cite Typed Stratego, DynSem, Dynamix
	x Anticipating proving correctness is a strong claim.

[^x] Lots of background makes it hard to follow

[~] Lack of concrete motivation

Review 3:

[~] Stack allocation would be nice -> actually, it was already there...
[^x] Hefty Algebras reference
[~] Description of the nanopass framework needs to be expanded to help understanding the value of the contribution.
[^x] "Eelco was looking for ..." needs reference

[^x] Explain background: e.g. monadic >>= and >>.
[x] Work related to future work should be in the future work section, not in related work.

Review 4:

[~] Why not `[[let(e,f)]] = [[e]] >>= \x. [[f x]]` -> because: different evaluation strategies (also already in the text)
[x] Is PHOAS purely presentational or essential? -> presentational, but also engrained into most effect libraries
[~] Have you run the generated machine code? If you did you should mention that! -> no, I don't have the time

Review 5 (summary):

[x] add more background
[~] provide a more concrete motivation
[x] check claims