# Revision history for netter

## 0.1.0.0  -- 2020-02-02

* First version.

## 0.1.1.0  -- 2020-05-27

* Block-scoped local variables

* Expression evaluation

* List indexing

* ... many other features.

## 0.1.2.0 -- 2020-06-05

* Generalize indexing operations to arbitrary functors keyed by integer

## 0.2.0.0 -- 2020-07-13

* New verified inlining and variable elimination ("trimming") passes

* Remove `formula`

## 0.3.0.0 -- 2020-08-13

* Minimize generated formulas during inlining.

* Refine the `--inlining` option to control which variables are inlined.

## 0.3.1.0 -- 2020-09-10

* Add negation operator

## 0.3.2.0 -- 2020-09-23

* Rename package from "randc" to "netter".

## 0.3.3.0

* Allow models to process custom command-line options through the `other` field.

* Remove double negation during simplification.
