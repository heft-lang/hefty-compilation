\documentclass[sigplan,anonymous,review]{acmart}

%include polycode.fmt

% \bibliographystyle{plainurl}% the mandatory bibstyle

\usepackage{todonotes}

\title{Compiling Effects}

\author{Jaro S. Reinders} % {Delft University of Technology, Netherlands}{j.s.reinders@tudelft.nl}{https://orcid.org/0000-0002-6837-3757}{} % (Optional) author-specific funding acknowledgements}

\begin{document}

\begin{abstract}

\end{abstract}

\maketitle

\section{Introduction (1 page)} \label{sec:intro}

Definitional interpreters are a popular approach to defining the dynamic semantics of programming languages (cite{ reynolds}).
Effects and handlers can be used to build interpreters from off-the-shelf language components (cite{ latent effects}).
To avoid interpretive overhead we are also interested in implementing compilers for languages defined this way.
We show how effects and handlers can be used as intermediate representations for producing efficient machine code.

\todo[inline]{There is a lot of literature on converting interpreters to abstract machines (and then compilers?) and partial evaluation (Futamura). Should I mention that here?}

\todo[inline]{Transition from last paragraph to the following.}

For example we can define the abstract syntax and dynamic semantics of a simple expression language with integers and addition as follows:

% < data L = Num Int | Plus L L
% < 
% < eval :: L -> Int
< eval (Num n) = n
< eval (Plus x y) = eval x + eval y

A problem arises when trying to extend such language definitions.
Consider the addition of language constructs for let bindings and variables.
We would have to completely rewrite the interpreter,
for example as follows:

% < data L = Num Int | Plus L L | Let String L L | Var String
% <
% < type Env = String -> Int
% <
% < insert :: String -> Int -> Env -> Env
% < insert v x env v' = if v == v' then x else env v'
% < 
% < eval :: Env -> L -> Int
< eval env (Num n) = n
< eval env (Plus x y) = eval env x + eval env y
< eval env (Let v x y) = eval (insert v (eval env x) env) y
< eval env (Var v) = lookup v env

\todo[inline]{Aren't variables part of the values that can be returned, e.g. |data Value = VNum Int || VVar String|? Do we need to change this code?}

Even the cases that do not deal with the environment still need to take the environment as an argument and pass it to recursive calls.

Using effects we can avoid this problem and write our interpreter as two separate functions:

%format L_Arith
%format eval_Arith
%format L_Let
%format eval_Let

%format return = "\mathbf{return}"
%format effect = "\mathbf{effect}"
%format D = "\Delta"
%format ==> = "\Rrightarrow"
%format handler = "\mathbf{handler}"
%format |-> = "\mapsto"
%format handle = "\mathbf{handle}"
%format with = "\mathbf{with}"
%format let = "\mathit{let}"

% < data L_Arith a = Num Int | Plus a a
% <
% < eval_Arith : L_Arith (Int ! D) -> Int ! D
< eval_Arith (Num n) = return n
< eval_Arith (Plus mx my) = do
<   x <- mx
<   y <- my
<   return x + y
% <
% < data L_Let a = Let String a a | Var String
% <
% < effect Reader r where
% <   ask : r ! Reader r, D
% <   local : (r -> r) -> a ! Reader r, D -> a ! Reader r, D
% <
% < eval_Let : L_Let (Int ! Reader Env, D) -> Int ! Reader Env, D
< eval_Let (Let v mx my) = do
<   x <- mx
<   local (insert v x) my
< eval_Let (Var v) = asks (lookup v)

% <
% < hEnv : Env -> a ! Env, D => a ! D
% < hEnv env (withInsert v x my; k) = do
% <   y <- with hEnv (insert v x env) handle my
% <   k y
% < hEnv env (lookup v; k) = do k (env v)

Now |eval_Arith| does not have to mention environments.

Once we, as programming language designers, are satisfied with our modular definitional interpreter,
a natural question to ask ourselves is whether we can implement this language more efficiently.
In particular, can we write a compiler for this language that produces efficient machine code?

To answer this question, we use the definitional interpreter as a basis.
The effects framework allows us to transform our definitional interpreter gradually into a compiler.
First we need to abstract from concrete functions in the defining language, such as |+|, |insert|, and |lookup|.

< eval_Arith (Num n) = return n
< eval_Arith (Plus mx my) = do
<   x <- mx
<   y <- my
<   plus x y
<
< eval_Let (Let v mx my) = do
<   x <- mx
<   let v x my
< eval_Let (Var v) = var v

Now our defining language is just the effect system itself.

\todo[inline]{
At this point there are two variable binding mechanisms:
the monadic bindings |x <- mx|, and the |let| and |var| operations.
I could try to merge them, but then I'm afraid I'll be mixing the defining and the defined language.
Alternatively, I could try to make the |let| and |var| mechanism more first class.
Neither really sounds easy or elegant.
}

% OLD STORY:
% Modern compilers for mature programming languages commonly consist of hundreds of thousands to tens of millions lines of code.
% At the same time, programming languages are still very actively developed.
% In the last 12 years many new programming languages have appeared, such as Kotlin, Rust, and Swift.
% Rewriting all those lines of code for each new language is very costly.
% It is not a coincidence that all three languages are built on top of mature compiler platforms such as the JVM and LLVM.
% 
% However, the interface of these platforms, the intermediate representations (IR), are all monolithic and therefore limited to a single level of abstraction.
% That means that languages often still need to use a separate IR at a different level of abstraction for their own language specific transformations and optimizations.
% 
% How can we design a compiler platform which allows for maximum reuse across a large variety of programming languages?
% 
% The most important aspect of a compiler framework is the intermediate representation(s).
% An intermediate representation is the data structure that is used by the compiler to represent programs.
% 
% The approach we present is based on ideas that have a long history in the literature, namely denotational semantics, monads, and algebraic effects.
% It is no coincidence that the theory of programming language semantics plays a role in our compiler framework, because compilation is essentially a way of giving a semantics to a programming language.
% Monads and algebraic effects are related concepts that make it possible to define denotational semantics in a modular way.



% Moggi later introduced monads and monad morphisms to enable the modular definition of denotational semantics.
% Plotkin and Power presented a more ergonomic alternative to monad morphisms which just considered abstract algebraic effect interfaces.
% Plotkin and Pretnar made it possible to define practical programs in this paradigm of algebraic effects by introducing handlers which give semantics to the abstract operations of algebraic effects.
% Wu, Schrijvers, and Hinze observed that some language constructs such as exception catching did not fit into the algebraic effect framework and proposed a framework for more general scoped effects that does support exceptions.
% Van den Berg, Schrijvers, Bach Poulsen, and Wu observe yet more language constructs which do not fit into the algebraic effect framework and not even in the scoped effect framework.
% They introduce latent effects which are more general still.
% 
% Denotational semantics is about defining the meaning of programs by mapping the programs onto mathematical objects.
% Strachey's original school of thought exclusively used the lambda calculus the mathematical object to map programs onto, even before Scott proved that the lambda calculus is really a mathematical object. 
% Moggi's monads allow one to abstract over common patterns in these mappings which makes it easier to define the mapping.
% Monad morphisms allow for combining different monads in the same mapping, making the mapping modular. 

Directions (roughly in order of difficulty):
\begin{enumerate}
  \item Ergonomic IR for education. Requires contrasting with nanopass and Siek's book. Prior work: Nanopass compilation for education.
  \item Modular IR for reusability. Requires nontrivial compilers for multiple languages sharing many components. Prior work: Bridging the Gulf
  \item Efficient IR for optimizations. Requires efficient implementations of optimizations. Prior work: Compiling with Continuations, or without. Whatever!
  \item Formal Verification. Requires proofs of correctness of compilation. Prior work: Interaction Trees.
\end{enumerate}

\begin{itemize}
  \item What are the main ideas behind this paper?
  \item Why is it different from previous work?
\end{itemize}

Concretely, our contributions are:
\begin{itemize}
  \item We show how to build a modular compiler from a small language to a subset of X86 in Section~\ref{sec:simple-lang}.
  \item We demonstrate analyses and transformation over our modular IR in Section~\ref{sec:analysis}.
  \item We demonstrate the modularity of our approach by extending our compiler with conditionals and loops in Section~\ref{sec:cond-loops}.
  \item We evaluate our approach by compiling a suite of example programs and observing the behavior of the resulting binaries in Section~\ref{sec:evaluation}
\end{itemize}

\section{Effects and Handlers (3 page)} \label{sec:effects-handlers}

In this section we explain what effects and handlers are and show how they can be used in the context of compilers.

\begin{itemize}
  \item Keep high level
  \item Explain what the signatures are
  \item Show example program with high level effect like Arith and I/O and an equivalent program in X86 with variables (show types)
  \item High level overview of the whole approach
  \item Show effectful definitional interpreters
  \item Foreshadow reuse and other nice properties by using interpreters over multiple passes (maybe even full pipeline)
  \item (higher order functions would be nice)
\end{itemize}

\section{Syntactic Representation of Free Monads (1 page)}
  
\begin{itemize}
\item Show Free Monad refer to DTC
\item Show why the higher order representation is problematic
\end{itemize}

\section{Compiling a Simple Language to X86 (1 pages)} \label{sec:simple-lang}

In this section we introduce a simple language and show how it can be compiled to X86 with variables.

\section{Register Allocation (2 pages)} \label{sec:analysis}

In this section we show how we can remove the variables from our X86 representation.
This also serves as a demonstration of running an analysis over our modular IR.

\section{Adding Conditionals and Loops (2 pages)} \label{sec:cond-loops}

In this section we show that we can extend our language with new concepts without modifying code we have already written.

\section{Evaluation (1 pages)} \label{sec:evaluation}

In this section we evaluate the correctness of our compilers.

\begin{itemize}
  \item Use Siek's examples
\end{itemize}

\section{Related Work (1/2 page)} \label{sec:related}

\begin{itemize}
  \item MLIR
  \item nanopass compilation
  \item Hefty Algebras
  \item Using a monadic intermediate representation has been a successful research direction (Benton's, Hughes', and Moggi's "Monads and Effects" has many references, and https://www.habit-lang.org/ uses a monadic intermediate language MIL)
  \item QuickCheck IO paper to verify algebraic laws
\end{itemize}

% The most similar work seems to be Laurence Day's PhD thesis.
% He sticks to monad transformers for his interpreters, but essentially uses a free monad for compilation.
% Namely:
% 
% \begin{code}
% type Code = Fix (ARITH :+: EXCEPT :+: NULL)
% compArith :: Arith (Code -> Code) -> Code -> Code
% compExcept :: Except (Code -> Code) -> Code -> Code
% \end{code}
% 
% His running example are these two components: Arith and Except.
% The way he implements except in his target language is a bit suspect.
% He essentially pushes the handler 'Code' to the stack and pops it later.
% I think it would make more sense to push a reference to the handler 'Code' instead of the code itself.
% Does that invalidate his claims that he is building a compiler or is that just a minor implementation detail?
% He also presents a way to avoid this problem but that is just exploiting the fact that the handler is statically known for each exception that is thrown.
% 
% Interestingly, the fact that Laurence has to use 'Code' this way breaks modularity.
% That is very similar to our need for higher order effects.
% 
% One thing our approaches have in common is that we both need to represent jumps as a graph.
% He uses a PHOAS graph representation built into the fixed point type he uses, where I use a syntactic 'Blocks' effect.
% 
% Day uses a higher order functor representation to be able to distinguish expressions (which push their result to the stack) from statements (which leave the stack unchanged).
% I think Conal Elliot's calculating compilers categorically solves this in a better way by just using only statements.
% I haven't encountered this problem in my approach at all yet. Perhaps because I'm compiling to X86 and not a stack language.


\section{Conclusion and Future Work(1/2 page)} \label{sec:conclusion}

Future work:
\begin{itemize}
  \item Formal verification
\end{itemize}

\end{document}