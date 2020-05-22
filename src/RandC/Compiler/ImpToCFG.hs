module RandC.Compiler.ImpToCFG where

import RandC.Dependencies
import RandC.Options
import RandC.G
import RandC.Pass
import qualified RandC.Imp as Src
import qualified RandC.CFG as Tgt

import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State

type S a = State (Tgt.Id, M.Map Tgt.Id Tgt.Block) a

putBlock :: Tgt.Id -> Tgt.Block -> S ()
putBlock id block = do
  (maxId, blocks) <- get
  put (maxId, M.insert id block blocks)

newBlock :: Tgt.Block -> S Tgt.Id
newBlock block = do
  (maxId, blocks) <- get
  put (maxId + 1, M.insert maxId block blocks)
  return maxId

compileCom :: StateDeps -> Src.Com -> G Tgt.Id -> S (G Tgt.Id)
compileCom deps (Src.Com is) id = compileInstrs deps is id

compileInstrs :: StateDeps -> [Src.Instr] -> G Tgt.Id -> S (G Tgt.Id)
compileInstrs _ [] next =
  return next
compileInstrs deps (Src.Assn assn : is) next = do
  cNext <- compileInstrs deps is next
  let cNextDeps = guardedStateDeps deps (\_ _ -> S.empty) cNext
  -- If the next PC value depends on a variable that is updated by the
  -- assignment, we have to create a dummy block for the conditional.
  if S.disjoint (M.keysSet assn) cNextDeps then do
    id <- newBlock (Tgt.Block assn cNext)
    return $ return id
  else do
    id <- newBlock (Tgt.Block M.empty cNext)
    id <- newBlock (Tgt.Block assn (return id))
    return $ return id

compileInstrs deps (Src.If e cThen cElse : is) next = do
  cMergeNext <- compileInstrs deps is next
  cThenNext  <- compileCom deps cThen  cMergeNext
  cElseNext  <- compileCom deps cElse  cMergeNext
  return (If e cThenNext cElseNext)

compile :: Src.Program -> Pass Tgt.Program
compile prog = do
  Src.Program decls defs rews com <- ensureTarget CFG prog
  -- In principle we should not have to compute this value again, since we
  -- compute it already when optimizing the program.  However, the dependency
  -- map could be invalidated after applying certain program transformations, so
  -- it is safer to just recompute it.  If this turns out to be too slow, we can
  -- always cache this somewhere in the future.
  let deps = definitionStateDeps defs
  let initialState = (1, M.empty) -- We skip 0 since it will be the entry point of the program
  let res = compileCom deps com (return 0)
  let (next, (maxId, blocks)) = runState res initialState
  let initialBlock = Tgt.Block M.empty next
  let blocks' = M.insert 0 initialBlock blocks
  return $ Tgt.Program decls defs rews maxId blocks'
