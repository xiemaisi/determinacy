Mechanisation of Soundness Proof
================================

This directory contains a mechanisation of the soundness proof of our dynamic determinacy analysis.

Use the Makefile to compile the proofs; they were developed under Coq version 8.3pl4.

The Coq lemmas corresponding to the lemmas from the supporting material are annotated with comments.

The individual modules contain the following:

  * Common.v: a kitchen sink containing some generally useful definitions and lemmas

  * Eq.v: a Haskell-like Eq type class with some auxiliary results

  * FinMap.v: an implementation of finite maps as association lists; used to model environments

  * Parameters.v: declarations of unspecified sets and operations the semantics depends on

  * Syntax.v: the syntax of MuJS

  * Values.v: data types of concrete values, records, environments, heaps and events

  * Wf.v: well-formedness of values, records, environments, heaps and events

  * ConcreteSemantics.v: the concrete reduction relation

  * Domains.v: variable and property domains

  * InstrumentedValues.v: data types of instrumented values, records, environments, heaps and events

  * Modelling.v: definition of the modelling relation

  * DeterminacyOrder.v: definition of the ``more determinate than'' preorder

  * Discharging.v: functions for discharging determinacy annotations on values, records, environments, heaps and events

  * Substruct.v: definition of the substructure relation

  * Clobbering.v: definition of the clobbering operators \hat{\rho}[V:=\hat{\rho}^d] and \hat{h}[A:=\hat{h}^d]

  * Reverting.v: definition of the reverting operators \hat{\rho}'[V:=\hat{\rho}^?] and \hat{h}'[V:=\hat{h}^?]

  * InstrumentedSemantics.v: the instrumented reduction relation

  * Soundness.v: the soundness result