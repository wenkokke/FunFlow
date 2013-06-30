{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module FUN.Parsing where

import FUN.Base

import Prelude hiding ( abs, sum )
import Data.Char (isSpace)
import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.Utils
import Text.ParserCombinators.UU.Idioms (iI,Ii (..))
import Text.ParserCombinators.UU.BasicInstances (Parser,pSym)

-- * Parsing the FUN language

pProg :: Parser Prog
pProg = Prog <$> pDecls

pDecl :: Parser Decl
pDecl = iI decl pIdent (pListSep pSpaces pIdent) "=" pExpr Ii

pDecls :: Parser [Decl]
pDecls = pList1Sep (pSymbol ";") pDecl

pExpr :: Parser Expr
pExpr = (pAbs <|> pFix <|> pITE <|> pLet <|> pCon <|> (pSumL <|> pSumR) <|> pDes) <<|> pBin
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
  pLet = iI letn "let" pDecls "in" pExpr Ii
  pCon = iI con pConst (pParens $ pList2Sep pComma pExpr) Ii
  pSumL = iI (sum L) "L_" pConst pExpr Ii
  pSumR = iI (sum R) "R_" pConst pExpr Ii
  pDes = iI des "case" pExpr "of" pConst (pParens $ pList2Sep pComma pIdent) "in" pExpr Ii
  pITE = iI ITE "if" pExpr "then" pExpr "else" pExpr Ii
  
  -- chained expressions
  pApp = pChainl_ng (App <$ pSpaces) pAtom
  pBin = pChainl_ng (bin <$> pOper) pApp
  
pIdent,pConst,pOper :: Parser Name
pIdent = lexeme $ (:) <$> pLower <*> pMany (pLetter <|> pDigit <|> pUnderscore)
pConst = lexeme $ (:) <$> pUpper <*> pMany (pLetter <|> pDigit <|> pUnderscore)
pOper  = lexeme $ pSome $ pAnySym "!#$%&*+./<=>?@\\^|-~:"

pUnderscore :: Parser Char
pUnderscore = pSym '_'

-- * Recognising more list structures with separators

pFoldr2Sep :: IsParser p => (a -> b -> b, b) -> p a1 -> p a -> p b
pFoldr2Sep alg@(op,e) sep p = must_be_non_empties "pFoldr2Sep" sep p pfm
  where pfm = op <$> p <*> pFoldr1 alg (sep *> p)

pList2Sep :: IsParser p => p a1 -> p a -> p [a]
pList2Sep s p = must_be_non_empties "pListSep" s p (pFoldr2Sep list_alg s p)
