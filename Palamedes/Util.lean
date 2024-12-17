import Lean

open Lean Lean.Expr Lean.Meta

def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  withTheReader Core.Context (fun ctx => { ctx with options := ctx.options.setBool `smartUnfolding false }) do
  ppExpr (← withTransparency md $ reduce (.const c []))
