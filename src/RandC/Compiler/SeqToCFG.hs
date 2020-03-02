module RandC.Compiler.SeqToCFG where

import RandC.Options
import RandC.G
import RandC.Pass
import qualified RandC.Seq as Src
import qualified RandC.CFG as Tgt

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

compileCom :: Src.Com -> G Tgt.Id -> S (G Tgt.Id)
compileCom Src.Skip next =
  return next
compileCom (Src.Assn assn c) next = do
  cNext <- compileCom c next
  id <- newBlock (Tgt.Block (return assn) cNext)
  return $ return id
compileCom (Src.If e cThen cElse cMerge) next = do
  cMergeNext <- compileCom cMerge next
  cThenNext  <- compileCom cThen  cMergeNext
  cElseNext  <- compileCom cElse  cMergeNext
  return (If e cThenNext cElseNext)
compileCom (Src.Choice v es c) next = do
  cNext <- compileCom c next
  id <- newBlock (Tgt.Block (M.singleton v <$> es) cNext)
  return $ return id

compile :: Src.Program -> Pass Tgt.Program
compile prog = do
  Src.Program decls com <- ensureTarget CFG prog
  let initialState = (1, M.empty) -- We skip 0 since it will be the entry point of the program
  let res = compileCom com (return 0)
  let (next, (maxId, blocks)) = runState res initialState
  let initialBlock = Tgt.Block (return M.empty) next
  let blocks' = M.insert 0 initialBlock blocks
  return $ Tgt.Program decls maxId blocks'
