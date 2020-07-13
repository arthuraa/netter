module RandC.FFun where

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M

data FFun k a = FFun (k -> a) (Map k a)

insert :: Ord k => k -> a -> FFun k a -> FFun k a
insert k x (FFun def m) = FFun def (M.insert k x m)

supp :: (Ord k, Eq a) => FFun k a -> Set k
supp (FFun def m) = M.keysSet $ M.filterWithKey (\k v -> v /= def k) m

(!) :: Ord k => FFun k a -> k -> a
(!) (FFun def m) k = M.findWithDefault (def k) k m

mkffun :: Ord k => (k -> a) -> Map k a -> FFun k a
mkffun def ps = FFun def ps
