# PiCore_Noninterference

## What is this repository for?

This project contains the Isabelle/HOL formalisation and soundness proof for an event-based rely-guarantee reasoning framework for information flow security. It constains a case study, i.e., the IPC mechanism of ARINC 653 multicore.

## How do I get set up?

The project is developed by Isabelle/HOL 2023, older version may need some slight adjustments. You can load theorems by dragging them in the Isabelle/HOL GUI

## Layout

Semantics and Reasoning Framework

Ann_PiCore_Language, Ann_PiCore_Semantics, Ann_PiCore_Computation : semantics for imperative language
Ann_PiCore_Validity, Ann_PiCore_Hoare : proof rules and soundness proof of annotated rely-guarantee framework
Ann_PiCore_IFS : IFS definition and unwinding theorem
Ann_PiCore_RG_Prop : auxilliary lemma for soundness proof for IFS proof framework
Ann_PiCore_RG_IFS : proof rules and soundness proof of IFS reasoning framework
Ann_PiCore_Syntax : Syntax definition

## Case Study

ARINC653_MultiCore_Que : IPC mechanism for ARINC 653 multicore
