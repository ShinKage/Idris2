module Core.InitPrimitives

import Compiler.CompileExpr

import Core.Context
import Core.Primitives
import Core.TT

%default covering

addPrim : {auto c : Ref Ctxt Defs} ->
          {auto o : Ref OptCache OptimizationsCache} ->
          Prim -> Core ()
addPrim p
    = do addBuiltin (opName (fn p)) (type p) (totality p) (fn p)
         compileDef (opName (fn p))

export
addPrimitives : {auto c : Ref Ctxt Defs} -> Core ()
addPrimitives
    = do o <- newRef OptCache initOptimizationsCache
         traverse_ addPrim allPrimitives
