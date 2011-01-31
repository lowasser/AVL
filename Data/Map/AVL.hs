{-# LANGUAGE CPP #-}
module Data.Map.AVL where

import Data.Map.AVL.Internals

insertWithKey :: Ord k => (k -> a -> a -> a) -> k -> a -> SNode d k a -> Res d k a
insertWithKey _ k a NIL = res' $ singleton k a
insertWithKey f k a R(kx x l r) = case compare k kx of
  LT	-> joinL kx x (insertWithKey f k a l) r
  EQ	-> res (bin kx (f kx a x) l r)
  GT	-> joinR kx x l (insertWithKey f k a r)
insertWithKey f k a B(kx x l r) = case compare k kx of
  LT	-> joinL kx x (insertWithKey f k a l) r
  EQ	-> res (bin kx (f kx a x) l r)
  GT	-> joinR kx x l (insertWithKey f k a r)
insertWithKey f k a L(kx x l r) = case compare k kx of
  LT	-> joinL kx x (insertWithKey f k a l) r
  EQ	-> res (bin kx (f kx a x) l r)
  GT	-> joinR kx x l (insertWithKey f k a r)

insertMin, insertMax :: k -> a -> SNode d k a -> Res d k a
insertMin k a NIL		= res' $ singleton k a
insertMin k a L(kx x l r)	= joinL kx x (insertMin k a l) r
insertMin k a B(kx x NIL ~NIL)	= res' (bin kx x (singleton k a) nil)
insertMin k a B(kx x l r)	= joinL kx x (insertMin k a l) r
insertMin k a R(kx x NIL r)	= res (bin kx x (singleton k a) r)
insertMin k a R(kx x l r)	= joinL kx x (insertMin k a l) r

insertMax k a NIL		= res'  $ singleton k a
insertMax k a L(kx x l NIL)	= res (bin kx x l (singleton k a))
insertMax k a L(kx x l r)	= joinR kx x l (insertMax k a r)
insertMax k a B(kx x ~NIL NIL)	= res' (bin kx x nil (singleton k a))
insertMax k a B(kx x l r)	= joinR kx x l (insertMax k a r)
insertMax k a R(kx x l r)	= joinR kx x l (insertMax k a r)

#define DFMINRECURSE let !(k, a, l') = deleteFindMin l in (k, a, joinL kx x l' r)

deleteFindMin, deleteFindMax :: SNode (Succ d) k a -> (k, a, Res d k a)
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

#define GLUE if sz l >=# sz r then let !(k, a, l') = deleteFindMax l in joinL k a l' r else \
	let !(k, a, r') = deleteFindMin r in joinR k a l r'

glue :: SNode d k a -> SNode d k a -> Res d k a
glue l r | l `seq` r `seq` False	= undefined
glue NIL _		= res nil
glue l@L(_ _ _ _) r	= GLUE
glue l@B(_ _ _ _) r	= GLUE
glue l@R(_ _ _ _) r	= GLUE