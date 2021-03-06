{-# LANGUAGE GADTs, MultiParamTypeClasses, EmptyDataDecls, FunctionalDependencies, FlexibleInstances, MagicHash, Rank2Types, CPP #-}
{-# LANGUAGE BangPatterns, FlexibleContexts #-}
{-# OPTIONS -funbox-strict-fields #-}
module Data.Map.AVL.Internals (module Data.Map.AVL.Internals) where

import GHC.Exts

data Zero
data Succ d

data SNode d k a = SNode {sz :: !Int, node :: Node d k a}
data Node d k a where
  Nil :: Node Zero k a
  LeftBin :: k -> a -> !(SNode (Succ d) k a) -> !(SNode d k a) -> Node (Succ (Succ d)) k a
  Balanced :: k -> a -> !(SNode d k a) -> !(SNode d k a) -> Node (Succ d) k a
  RightBin :: k -> a -> !(SNode d k a) -> !(SNode (Succ d) k a) -> Node (Succ (Succ d)) k a

#define NIL (SNode _ Nil)
#define L(args) (SNode _ (LeftBin args))
#define B(args) (SNode _ (Balanced args))
#define R(args) (SNode _ (RightBin args))

data Res d k a = D !(SNode d k a) | DPlusOne !(SNode (Succ d) k a)

sNode :: Node d k a -> SNode d k a
sNode t = case t of
	Nil	-> SNode 0 Nil
	LeftBin _ _ l r
		-> SNode (sz l + sz r + 1) t
	RightBin _ _ l r
		-> SNode (sz l + sz r + 1) t
	Balanced _ _ l r
		-> SNode (sz l + sz r + 1) t

runRes :: Res d k a -> (SNode d k a -> r) -> (SNode (Succ d) k a -> r) -> r
runRes res f g = case res of
  D t	-> f t
  DPlusOne t -> g t

res :: SNode d k a -> Res d k a
res = D

resNode :: Node d k a -> Res d k a
resNode = res . sNode

res' :: SNode (Succ d) k a -> Res d k a
res' = DPlusOne

resNode' :: Node (Succ d) k a -> Res d k a
resNode' = res' . sNode

class Bin dL dR dOut | dL dR -> dOut where
  bin :: k -> a -> SNode dL k a -> SNode dR k a -> SNode dOut k a

class Join dL dR dOut where
  join :: k -> a -> SNode dL k a -> SNode dR k a -> Res dOut k a

instance Bin d d (Succ d) where
  bin k a l r = sNode (Balanced k a l r)

instance Join d d (Succ d) where
  join k a l r = res (bin k a l r)

instance Join d d d where
  join k a l r = res' (bin k a l r)

instance Bin d (Succ d) (Succ (Succ d)) where
  bin k a l r = sNode (RightBin k a l r)

instance Join d (Succ d) (Succ (Succ d)) where
  join k a l r = res (bin k a l r)

instance Join d (Succ d) (Succ d) where
  join k a l r = res' (bin k a l r)

instance Bin (Succ d) d (Succ (Succ d)) where
  bin k a l r = sNode (LeftBin k a l r)

instance Join (Succ d) d (Succ d) where
  join k a l r = res' (bin k a l r)
  
instance Join (Succ d) d (Succ (Succ d)) where
  join k a l r = res (bin k a l r)

instance Join (Succ (Succ d)) d (Succ (Succ d)) where
  join k a !L(lk la ll lr) !r = res (bin lk la ll (bin k a lr r))
  join k a !B(lk la ll lr) !r = res' (bin lk la ll (bin k a lr r))
  join k a !R(lk la ll L(lrk lra lrl lrr)) !r = res (bin lrk lra (bin lk la ll lrl) (bin k a lrr r))
  join k a !R(lk la ll B(lrk lra lrl lrr)) !r = res (bin lrk lra (bin lk la ll lrl) (bin k a lrr r))
  join k a !R(lk la ll R(lrk lra lrl lrr)) !r = res (bin lrk lra (bin lk la ll lrl) (bin k a lrr r))

instance Join d (Succ (Succ d)) (Succ (Succ d)) where
  join k a !l !R(rk ra rl rr) = res (bin rk ra (bin k a l rl) rr)
  join k a !l !B(rk ra rl rr) = res' (bin rk ra (bin k a l rl) rr)
  join k a !l !L(rk ra R(rlk rla rll rlr) rr) = res (bin rlk rla (bin k a l rll) (bin rk ra rlr rr))
  join k a !l !L(rk ra B(rlk rla rll rlr) rr) = res (bin rlk rla (bin k a l rll) (bin rk ra rlr rr))
  join k a !l !L(rk ra L(rlk rla rll rlr) rr) = res (bin rlk rla (bin k a l rll) (bin rk ra rlr rr))

{-# INLINE joinL #-}
joinL :: (Join dL dR dOut, Join (Succ dL) dR dOut) => k -> a -> Res dL k a -> SNode dR k a -> Res dOut k a
joinL k a l r = runRes l (\ l' -> join k a l' r) (\ l' -> join k a l' r)

{-# INLINE joinR #-}
joinR :: (Join dL dR dOut, Join dL (Succ dR) dOut) => k -> a -> SNode dL k a -> Res dR k a -> Res dOut k a
joinR k a l r = runRes r (join k a l) (join k a l)

nil :: SNode Zero k a
nil = SNode 0 Nil

singleton :: k -> a -> SNode (Succ Zero) k a
singleton k a = bin k a nil nil

deleteFindMin, deleteFindMax :: SNode (Succ d) k a -> (k, a, Res d k a)
#define DFMINRECURSE let !(k, a, l') = deleteFindMin l in (k, a, joinL kx x l' r)
deleteFindMin L(kx x l r)	= DFMINRECURSE
deleteFindMin B(kx x NIL _)	= (kx, x, res nil)
deleteFindMin B(kx x l@L(_ _ _ _) r) = DFMINRECURSE
deleteFindMin B(kx x l@B(_ _ _ _) r) = DFMINRECURSE
deleteFindMin B(kx x l@R(_ _ _ _) r) = DFMINRECURSE
deleteFindMin R(kx x NIL r)	= (kx, x, res r)
deleteFindMin R(kx x l@L(_ _ _ _) r) = DFMINRECURSE
deleteFindMin R(kx x l@B(_ _ _ _) r) = DFMINRECURSE
deleteFindMin R(kx x l@R(_ _ _ _) r) = DFMINRECURSE

#define DFMAXRECURSE let !(k, a, r') = deleteFindMax r in (k, a, joinR kx x l r')
deleteFindMax R(kx x l r)	= DFMAXRECURSE
deleteFindMax B(kx x _ NIL)	= (kx, x, res nil)
deleteFindMax B(kx x l r@L(_ _ _ _)) = DFMAXRECURSE
deleteFindMax B(kx x l r@B(_ _ _ _)) = DFMAXRECURSE
deleteFindMax B(kx x l r@R(_ _ _ _)) = DFMAXRECURSE
deleteFindMax L(kx x l NIL)	= (kx, x, res l)
deleteFindMax L(kx x l r@L(_ _ _ _)) = DFMAXRECURSE
deleteFindMax L(kx x l r@B(_ _ _ _)) = DFMAXRECURSE
deleteFindMax L(kx x l r@R(_ _ _ _)) = DFMAXRECURSE