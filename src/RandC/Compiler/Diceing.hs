module RandC.Compiler.Diceing where

import RandC.Options
import RandC.Pass
import RandC.Prob
import qualified RandC.Imp        as S
import qualified RandC.Dice       as T

import qualified Data.Map.Strict as M
import Control.Monad.ST
import Data.STRef

compile :: S.Program -> Pass T.Program
compile prog = do
  S.Program varDecls com <- ensureTarget Dice prog
  return $ runST $ do
    diceCount <- newSTRef 0
    dice      <- newSTRef M.empty

    let newDie ps = do
          c  <- readSTRef diceCount
          ds <- readSTRef dice
          writeSTRef diceCount $ c + 1
          writeSTRef dice      $ M.insert c ps ds
          return c

    let compileCom S.Skip =
          return $ T.Skip

        compileCom (S.Assn v e) =
          return $ T.Assn v (return e)

        compileCom (S.Seq c1 c2) = do
          c1' <- compileCom c1
          c2' <- compileCom c2
          return $ T.Seq c1' c2'

        compileCom (S.If e cThen cElse) = do
          cThen' <- compileCom cThen
          cElse' <- compileCom cElse
          return $ T.If (return e) cThen' cElse'

        compileCom (S.Choice v (P es)) = do
          d <- newDie $ map fst es
          return $ T.Assn v (Choice d [return e | (_, e) <- es])

    com' <- compileCom com
    ds   <- readSTRef dice

    return $ T.Program varDecls ds com'
