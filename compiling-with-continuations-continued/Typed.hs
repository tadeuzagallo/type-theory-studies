module Typed where

data Type
  = TUnit
  | TExn
  | TProd Type Type
  | TSum Type Type
  | TArrow Type Type

data Value
  = Unit
  | Pair Var Var
  | In Int Var

data Term
  = LetVal Var Value Term
  | LetProj Var Int Var Term
  | LetCont [ContDef] Term
  | LetFun [FunDef] Term
  | AppCont ContVar Var
  | App Var ContVar ContVar Var
  | Case Var ContVar ContVar

data FunDef = FunDef Var ContVar ContVar Var Term

data ContDef = ContDef ContVar Var Term
