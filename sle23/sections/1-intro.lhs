\section{Introduction}

Algebraic effects and handlers are a popular approach to programming with effects

The idea is to program against an interface of effectful operations

The actual implementation can be provided separately via \emph{effect handlers}

For example,

[...]

Benefit: composable, domain-specific effects

While languages are emerging with built-in support for this style of programming, the de facto standard way of defining algebraic effects in practice is to embed them as EDSLs in existing languages

Effect handlers in these EDSLs are usually defined as interpreters over a syntax of effectful operations

These interpreters are often slow in practice.

In this paper we consider how to eliminate this interpretive overhead by handling effects in a way that we \emph{compile} effectful operations into lower-level code that is efficiently executable

Challenges: some effects and some compiler passes require a syntactic approach; but effects and effect interfaces are often semantic in nature

In particular, operations are given by HOAS instead of FOAS

The benefit of HOAS is that we get hygiene for our effectful programs for free.

However, HOAS is not well-suited for static analysis, which many compiler passes rely on

Goal: define multi-pass compilers for domain-specific effects where each pass in the compiler has a clear and well-defined semantics given by algebraic effects

Support static analysis by systematically translating between HOAS and FOAS

Study reusable IRs and optimizations for different/related languages and domains (future work)

We build on previous work [POPL] which provides support for _higher-order effects_

Contributions:

1. Defining composable compilers that implement the semantics of simple domain-specific effects

2. Systematic translation between HOAS and FOAS

3. Demonstrate modularity by building a compiler for a small example language and adding conditionals

