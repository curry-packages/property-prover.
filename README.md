property-prover: A tool to verify properies of Curry programs
=============================================================

This package contains a tool to verify various properties
of Curry programs with a separate SMT solver.
It combines and extends two previous tools for Curry,
the `contract-prover` tool intended to statically verify
contracts in the form of pre- and postcondition
so that contract checks are not performed at run time,
and the `failfree` tool intended to verify that all operations
in a module are non-failing, i.e., their evaluation does not result
in a failure if they are called with arguments satisfying
the non-failing precondition of the operation.

Therefore, the ideas of each of these tools
is separately described below.

Static contract verification
----------------------------

This tool tries to verify and adds contract checking to Curry programs
by proving contracts with an SMT solver. If a proof is successful,
no contract check will be performed at run time, otherwise
a dynamic (strict) contract check will be added.
The static verification of contracts has the advantage that
the program is more reliable (if all contracts are verified)
or the resulting program will run more efficiently compared
to a program with dynamic contract checking only.

A detailed description of the ideas of this tool can be found in the
[journal paper](http://dx.doi.org/10.3233/FI-2020-1925}.

The contract verification tool can be invoked alone via

    > currvy --no-failfree <Curry module>

This analyzes the FlatCurry code of the module, attempts to prove
the contracts in this module (unless option `--checkmode=a` is set),
and adds dynamic contract checking if a proof is not successful.
Finally, the FlatCurry program is replaced by the transformed version
(unless option `--no-write` is set).
Hence, this tool might be integrated into the compilation chain
of a Curry system.
In addition to the transformation of the FlatCurry program,
successful proofs will be stored in files so that they can
be re-used by other tools. For instance, if the postcondition
of an operation `f` defined in module `M` is verified,
a file `PROOF_M_f_SatisfiesPostCondition.smt` is generated.
This file contains the SMT script of this proof.

The directory `examples/contracts` contains various examples where the
contract prover can eliminate all contracts at compile time.


Implementation
==============

In contrast to the first contract prover described in
[LOPSTR 2017 paper](https://dx.doi.org/10.1007/978-3-319-94460-9_19),
which tried to remove contracts added by the Curry preprocessor,
this version tries to verify contracts before they are added
to the Curry program and adds dynamic checks only for unverified contracts
(see the auxiliary operations defined in `include/ContractChecker.curry`).

The strategy is as follows:

1. For each postcondition `f'post`, try to verify it.
   If this is not successful, a dynamic check is added to `f`.

2. For each function call `(f args)`, where a preconditon `f'pre` exists,
   try to verify this precondition in the given context of the call.
   If it cannot be verified, transform the function call into

       checkPreCond (f args) (f'pre args) "f" (args)

   See `include/ContractChecker.curry` for the definition of `checkPreCond`.


Notes:
------

- Contracts can also be stored in separate files.
  When checking a module `m`, if there is a Curry module `m_SPEC`
  in the load path for module `m` or in the package directory `include`,
  the contents of `m_SPEC` is added to `m` before it is checked.

- Contracts for operators can also be specified by
  operations named by `op_xh1...hn'`, where each
  `hi` is a two digit hexadecimal number and the name
  of the operator corresponds to the ord values of `h1...hn`.
  For instance, a precondition for the operator `!!` can be named
  `op_x2121'pre`. To generate such names automatically,
  one can use the option `--name` of the tool.


Directories of the package:
---------------------------

* examples/contracts: some examples (and test suite)

* include: an include file for the SMT solver and a small Curry program
  containing operations which perform dynamic contract checking
  for unverified contracts

* src: source code of the implementation

---------------------------------------------------------------------------

Basic idea of the fail-free verification tool:
----------------------------------------------

The objective is this tool is to verify that all operations are non-failing,
i.e., their evaluation does not result in a failure, if they are called
with arguments satisfying the non-failing precondition of the operation.

Example:

    -- The operation `head` does not fail if this precondition is satisfied:
    head'nonfail xs = not (null xs)

    head (x:xs) = x

Note that the non-failing precondition is not a precondition for `head`,
i.e., it is still allowed to use `head` in a logical setting.
However, it can be used to verify that the following operation
is non-failing:

    readCommand = do
      putStr "Input a command:"
      s <- getLine
      let ws = words s
      if null ws then readCommand
                 else processCommand (head ws) (tail ws)

A detailed description can be found in the
[PPDP 2018 paper](https://doi.org/10.1145/3236950.3236957).
Basically, the following techniques are used to verify non-failing properties:

1. Test whether the operation is pattern-completely defined
   (i.e., branches on all patterns in all or-branches)
   for all inputs satisfying the non-failing precondition.
   If this is not the case, the operation is possibly failing.

2. Test whether the operations called in the right-hand side
   are used with satisfied non-failing preconditions
   for all inputs satisfying the non-failing precondition.

3. Test whether a call to `Prelude.failed` is unreachable, e.g., in

       abs x = if x>=0 then x
                       else if x<0 then (0 - x)
                                   else failed

   Note that this might be the result translating the following definition:

       abs x | x>=0 = x
             | x<0  = 0 - x

   This requires reasoning on integer arithmetic, as supported by SMT solvers.


Depending on the state of the operation `error`,
this could also avoid the occurrence of run-time errors:

    readLine = do
      putStr "Input a non-empty string:"
      s <- getLine
      if null s then error "Empty input!"
                else do putStr "First char: "
                        putStrLn (head s)

If `error` is considered as an always failing operation
(which is done if the option `--error` is set),
`readLine` cannot be verified as non-failing.
However, this requires also a careful analysis
of all external operations (like `readFile`)
which might raise exceptions.

---------------------------------------------------------------------------

Current restrictions:
---------------------

- The non-fail condition should be a Boolean formula, i.e.,
  not a function with pattern matching or local definitions.
  Furthermore, it should be a first-order equation, i.e.,
  in eta-expanded form.


---------------------------------------------------------------------------

Notes:
------

- Contracts and non-fail conditions can also be stored in separate
  files. When checking a module `m`, if there is a Curry module `m_SPEC`
  in the load path for module `m` or in the package directory `include`,
  the contents of `m_SPEC` is added to `m` before it is checked.

- Non-fail conditions for operators can also be specified by
  operations named by `op_xh1...hn'`, where each
  `hi` is a two digit hexadecimal number and the name
  of the operator corresponds to the ord values of `h1...hn`.
  For instance, the non-fail condition for `&>` can be named
  `op_x263E'nonfail`. To generate such names automatically,
  one can use the option `--name` of the tool.

- Operations defining contracts and properties are not verified.

- The SMT solver `z3` with at least version `4.7.1` must be in `PATH` for the
  tool to work properly.

---------------------------------------------------------------------------

Directories of the package:
---------------------------

* examples: some examples (and test suite)

* include: an include file for the SMT solver and non-fail conditions
  for various system modules

* src: source code of the implementation

---------------------------------------------------------------------------
