{-# LANGUAGE GADTs, MultiParamTypeClasses, EmptyDataDecls, FunctionalDependencies, FlexibleInstances, MagicHash, Rank2Types, CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS -funbox-strict-fields #-}
module Data.Map.AVL where

import GHC.Exts

data Zero
data Succ d

data SNode d k a = SNode {sz :: Int#, node :: Node d k a}
data Node d k a where
  Nil :: Node Zero k a
  LeftBin :: k -> a -> !(SNode (Succ d) k a) -> !(SNode d k a) -> Node (Succ (Succ d)) k a
  Balanced :: k -> a -> !(SNode d k a) -> !(SNode d k a) -> Node (Succ d) k a
  RightBin :: k -> a -> !(SNode d k a) -> !(SNode (Succ d) k a) -> Node (Succ (Succ d)) k a

#define L(args) (SNode _ (LeftBin args))
#define B(args) (SNode _ (Balanced args))
#define R(args) (SNode _ (RightBin args))

type Res d k a = forall r . (Int# -> Node d k a -> r) -> (Int# -> Node (Succ d) k a -> r) -> r

sNode :: Node d k a -> SNode d k a
sNode t = case t of
	Nil	-> SNode 0# Nil
	LeftBin _ _ l r
		-> SNode (sz l +# sz r +# 1#) t
	RightBin _ _ l r
		-> SNode (sz l +# sz r +# 1#) t
	Balanced _ _ l r
		-> SNode (sz l +# sz r +# 1#) t

res :: SNode d k a -> Res d k a
res (SNode sz# t) f _ = f sz# t

resNode :: Node d k a -> Res d k a
resNode = res . sNode

res' :: SNode (Succ d) k a -> Res d k a
res' (SNode sz# t) _ g = g sz# t

resNode' :: Node (Succ d) k a -> Res d k a
resNode' = res' . sNode

class Bin dL dR dOut | dL dR -> dOut where
  bin :: k -> a -> SNode dL k a -> SNode dR k a -> SNode dOut k a

class Bal dL dR dOut | dL dR -> dOut where
  bal :: k -> a -> SNode dL k a -> SNode dR k a -> Res dOut k a

instance Bin d d (Succ d) where
  bin k a l r = sNode (Balanced k a l r)

instance Bal d d (Succ d) where
  bal k a l r = res (bin k a l r)

instance Bin d (Succ d) (Succ (Succ d)) where
  bin k a l r = sNode (RightBin k a l r)

instance Bal d (Succ d) (Succ (Succ d)) where
  bal k a l r = res (bin k a l r)

instance Bin (Succ d) d (Succ (Succ d)) where
  bin k a l r = sNode (LeftBin k a l r)

instance Bal (Succ d) d (Succ (Succ d)) where
  bal k a l r = res (bin k a l r)

instance Bal (Succ (Succ d)) d (Succ (Succ d)) where
  bal k a !L(lk la ll lr) !r = res (bin lk la ll (bin k a lr r))
  bal k a !B(lk la ll lr) !r = res' (bin lk la ll (bin k a lr r))
  bal k a !R(lk la ll L(lrk lra lrl lrr)) !r = res (bin lrk lra (bin lk la ll lrl) (bin k a lrr r))
  bal k a !R(lk la ll B(lrk lra lrl lrr)) !r = res (bin lrk lra (bin lk la ll lrl) (bin k a lrr r))
  bal k a !R(lk la ll R(lrk lra lrl lrr)) !r = res (bin lrk lra (bin lk la ll lrl) (bin k a lrr r))

instance Bal d (Succ (Succ d)) (Succ (Succ d)) where
  bal k a !l !R(rk ra rl rr) = res (bin rk ra (bin k a l rl) rr)
  bal k a !l !B(rk ra rl rr) = res' (bin rk ra (bin k a l rl) rr)
  bal k a !l !L(rk ra R(rlk rla rll rlr) rr) = res (bin rlk rla (bin k a l rll) (bin rk ra rlr rr))
  bal k a !l !L(rk ra B(rlk rla rll rlr) rr) = res (bin rlk rla (bin k a l rll) (bin rk ra rlr rr))
  bal k a !l !L(rk ra L(rlk rla rll rlr) rr) = res (bin rlk rla (bin k a l rll) (bin rk ra rlr rr))