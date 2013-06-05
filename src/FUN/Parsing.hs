{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module FUN.Parsing where

import FUN.Base

import Prelude hiding (abs)
import Data.Char (isSpace)
import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.Utils
import Text.ParserCombinators.UU.Idioms (iI,Ii (..))
import Text.ParserCombinators.UU.BasicInstances (Parser,pSym)

-- * Parsing the FUN language

pIdent,pConst,pOper :: Parser Name

pIdent = lexeme $ (:) <$> pLower <*> pMany pLetter
pConst = lexeme $ (:) <$> pUpper <*> pMany pLetter
pOper  = lexeme $ pSome $ pAnySym "!#$%&*+./<=>?@\\^|-~:"

pExpr :: Parser Expr
pExpr = (pAbs <|> pFix <|> pITE <|> pLet <|> pCon <|> pDes) <<|> pBin
  where
  
  -- literal expressions
  pLit = Integer    <$> pInteger
     <|> Bool True  <$  pSymbol "true"
     <|> Bool False <$  pSymbol "false"
    
  -- atomic expressions
  pAtom = Lit <$> pLit
     <<|> Var <$> pIdent
     <<|> pParens pExpr
  
  -- simple expressions
  pAbs = iI abs "fun" (pList1Sep pSpaces pIdent) "=>" pExpr Ii
  pFix = iI fix "fix" (pList2Sep pSpaces pIdent) "=>" pExpr Ii
  pDef = iI (,) pIdent ":=" pExpr Ii
  pLet = iI letn "let" (pList1Sep pSemi pDef) "in" pExpr Ii
  pCon = iI Con pConst (pParens $ pListSep pComma pExpr) Ii
  pDes = iI Des "case" pExpr "of" pConst (pParens $ pListSep pComma pIdent) "in" pExpr Ii
  pITE = iI ITE "if" pExpr "then" pExpr "else" pExpr Ii
  
  -- chained expressions
  pApp = pChainl_ng (App <$ pSpaces) pAtom
  pBin = pChainl_ng (bin <$> pOper) pApp

-- * Recognising more characters

pSemi :: Parser Char
pSemi = lexeme $ pSym ';'

-- * Recognising more list structures with separators

pFoldr2Sep :: IsParser p => (a -> b -> b, b) -> p a1 -> p a -> p b
pFoldr2Sep alg@(op,e) sep p = must_be_non_empties "pFoldr2Sep" sep p pfm
  where pfm = op <$> p <*> pFoldr1 alg (sep *> p)

pList2Sep :: IsParser p => p a1 -> p a -> p [a]
pList2Sep s p = must_be_non_empties "pListSep" s p (pFoldr2Sep list_alg s p)
