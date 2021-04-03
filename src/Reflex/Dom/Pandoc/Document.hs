{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Reflex.Dom.Pandoc.Document
  ( elPandoc
  , elPandocInlines
  , elPandocBlocks
  , Config(..)
  , PandocRawNode(..)
  , defaultConfig
  ) where

import           Control.Monad                  ( join
                                                , void
                                                )
import           Control.Monad.Fix              ( MonadFix(..) )
import           Control.Monad.Reader           ( MonadReader(ask)
                                                , MonadTrans(lift)
                                                , ReaderT(runReaderT)
                                                )
import           Data.Bifunctor                 ( bimap )
import           Data.Bool                      ( bool )
import           Data.Dependent.Sum
import           Data.Foldable                  ( fold )
import           Data.Functor.Compose           ( Compose(..) )
import           Data.Functor.Identity          ( Identity(..) )
import           Data.GADT.Compare
import qualified Data.Map                      as Map
import           Data.Map.Strict                ( Map )
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Type.Equality             ( (:~:)(..) )
import           Reflex.Dom.Core         hiding ( Link
                                                , Space
                                                , mapAccum
                                                )
import           Reflex.Dom.Pandoc.Footnotes
import           Reflex.Dom.Pandoc.Raw          ( PandocRawNode(..)
                                                , elPandocRawNodeSafe
                                                )
import           Reflex.Dom.Pandoc.SyntaxHighlighting
                                                ( elCodeHighlighted )
import           Reflex.Dom.Pandoc.Util         ( elPandocAttr
                                                , headerElement
                                                , plainify
                                                , renderAttr
                                                , sansEmptyAttrs
                                                )
import           Text.Pandoc.Definition

data Config t m a = Config
  { -- | Custom link renderer.
    _config_renderLink
      :: m (Dynamic t a)
      ->
      -- Link URL
         Dynamic t Text
      ->
      -- Link attributes, including "title"
         Dynamic t (Map Text Text)
      ->
      -- Inner body of the link.
         Dynamic t [DSum InlineTag Identity]
      -> m (Dynamic t a)
  ,
    -- | How to render code blocks
    _config_renderCode :: m () -> Dynamic t Attr -> Dynamic t Text -> m ()
  ,
    -- | How to render raw nodes
    _config_renderRaw  :: Dynamic t PandocRawNode -> m a
  }

defaultConfig :: (PostBuild t m, DomBuilder t m) => Config t m ()
defaultConfig = Config (\f _ _ _ -> f >> pure (constDyn ()))
                       (\f _ _ -> f)
                       (dyn_ . fmap elPandocRawNodeSafe)

-- | Convert Markdown to HTML
elPandoc
  :: forall t m a
   . (DomBuilder t m, Monoid a, MonadHold t m, MonadFix m, PostBuild t m)
  => Config t m a
  -> Dynamic t Pandoc
  -> m (Dynamic t a)
elPandoc cfg doc = do
  let fs = queryFootnotes <$> doc
  x <- flip runReaderT fs $ renderBlocks cfg (pandocBlocks <$> doc)
  f <- renderFootnotes
    (sansFootnotes . renderBlocks cfg . fmap (fmap blockToDSum))
    fs
  pure (x <> join f)

pandocBlocks :: Pandoc -> [DSum BlockTag Identity]
pandocBlocks (Pandoc _meta blocks) = fmap blockToDSum blocks

-- | Render list of Pandoc inlines
elPandocInlines
  :: (PostBuild t m, MonadHold t m, MonadFix m, DomBuilder t m)
  => Dynamic t [Inline]
  -> m ()
elPandocInlines =
  void . sansFootnotes . renderInlines defaultConfig . fmap (fmap inlineToDSum)

-- | Render list of Pandoc Blocks
elPandocBlocks
  :: (PostBuild t m, DomBuilder t m, MonadHold t m, MonadFix m)
  => Dynamic t [Block]
  -> m ()
elPandocBlocks =
  void . sansFootnotes . renderBlocks defaultConfig . fmap (fmap blockToDSum)

mapAccum
  :: (DomBuilder t m, MonadHold t m, PostBuild t m, MonadFix m, Monoid a)
  => Dynamic t [v]
  -> (Dynamic t v -> m (Dynamic t a))
  -> m (Dynamic t a)
mapAccum xs f = do
  r <- simpleList xs f
  pure (mconcat =<< r)

mapAccumIndex
  :: (DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, Monoid a)
  => Dynamic t [v]
  -> (Int -> Dynamic t v -> m (Dynamic t a))
  -> m (Dynamic t a)
mapAccumIndex xs f = do
  mapAccum' (Map.fromAscList . zip [0 ..] <$> xs) f

mapAccum'
  :: (DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, Ord k, Monoid a)
  => Dynamic t (Map k v)
  -> (k -> Dynamic t v -> m (Dynamic t a))
  -> m (Dynamic t a)
mapAccum' xs f = do
  r <- listWithKey xs f
  pure (fold <$> joinDynThroughMap r)

dynDyn
  :: (DomBuilder t m, PostBuild t m, MonadHold t m, Monoid a)
  => Dynamic t (m (Dynamic t a))
  -> m (Dynamic t a)
dynDyn dynWidget = do
  ev   <- dyn dynWidget
  dynr <- holdDyn (constDyn mempty) ev
  pure $ join dynr

renderBlocks
  :: (DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m, Monoid a)
  => Config t m a
  -> Dynamic t [DSum BlockTag Identity]
  -> ReaderT (Dynamic t Footnotes) m (Dynamic t a)
renderBlocks cfg xs = mapAccum xs $ \x -> do
  x' <- factorDyn x
  dynDyn $ fmap (renderBlock cfg) x'

renderBlock
  :: (DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, Monoid a)
  => Config t m a
  -> DSum BlockTag (Compose (Dynamic t) Identity)
  -> ReaderT (Dynamic t Footnotes) m (Dynamic t a)
renderBlock cfg = \case
  PlainTag :=> Compose xs -> do
    mapAccumIndex (runIdentity <$> xs) $ \k v -> do
      v' <- factorDyn v
      dynDyn $ fmap (renderInlinesCheckbox k) v'
  ParaTag :=> Compose xs -> do
    el "p" $ mapAccumIndex (runIdentity <$> xs) $ \k v -> do
      v' <- factorDyn v
      dynDyn $ fmap (renderInlinesCheckbox k) v'
  LineBlockTag :=> Compose xss -> do
    mapAccum (runIdentity <$> xss) $ \xs -> do
      renderInlines cfg xs <* text "\n"
  CodeBlockTag :=> Compose dynxs ->
    let (attr, x) = splitDynPure (runIdentity <$> dynxs)
    in  do
          lift $ _config_renderCode cfg (elCodeHighlighted attr x) attr x
          pure mempty
  RawBlockTag :=> Compose x ->
    lift
      $  _config_renderRaw cfg (uncurry PandocRawNode_Block . runIdentity <$> x)
      >> pure mempty
  BlockQuoteTag :=> Compose xs ->
    el "blockquote" $ renderBlocks cfg (fmap runIdentity xs)
  OrderedListTag :=> Compose dynxs ->
    let (attrs, xss)    = splitDynPure (runIdentity <$> dynxs)
        (idx, style, _) = splitDyn3Pure attrs
    in  do
-- delimStyle is not supported in HTML or in Semantic UI
          elDynAttr "ol" (fmap listStyle style <> fmap startFrom idx) $ do
            mapAccum xss $ \xs -> do
              el "li" $ renderBlocks cfg xs
  BulletListTag :=> Compose xss ->
    el "ul" $ mapAccum (runIdentity <$> xss) $ \xs ->
      el "li" $ renderBlocks cfg xs
  DefinitionListTag :=> Compose defs ->
    el "dl" $ mapAccum (runIdentity <$> defs) $ \xs ->
      let (term, descList) = splitDynPure xs
      in  do
            x <- el "dt" $ renderInlines cfg term
            fmap (x <>) $ mapAccum descList $ \desc ->
              el "dd" $ renderBlocks cfg desc
  HeaderTag :=> Compose dynxs ->
    let (dynLevel, attr, xs) = splitDyn3Pure (runIdentity <$> dynxs)
    in  dynDyn
          $   (\level -> elPandocAttr (headerElement level) attr $ do
                renderInlines cfg xs
              )
          <$> dynLevel

  HorizontalRuleTag :=> Compose _ -> el "hr" blank >> pure mempty
  TableTag :=> Compose dynxs ->
    let --(attr, _captions, _colSpec, TableHead _ hrows, tbodys, _tfoot) -> do
      attr   = (\(x, _, _, _, _, _) -> x) . runIdentity <$> dynxs
      hrows  = (\(_, _, _, TableHead _ x, _, _) -> x) . runIdentity <$> dynxs
      tbodys = (\(_, _, _, _, x, _) -> x) . runIdentity <$> dynxs
    in
      do
-- TODO: Apply captions, colSpec, etc.
        elPandocAttr "table" attr $ do
          x <- el "thead" $ do
            mapAccum hrows $ \dynRows ->
              let cells = (\(Row _ x) -> x) <$> dynRows
              in
                do
                  el "tr" $ do
                    mapAccum cells $ \dynCells ->
                      let blks = (\(Cell _ _ _ _ y) -> y) <$> dynCells
                      in
                        do
                          el "th"
                            $ renderBlocks cfg (fmap (fmap blockToDSum) blks)
          fmap (x <>) $ mapAccum tbodys $ \dynBodys ->
            let rows = (\(TableBody _ _ _ w) -> w) <$> dynBodys
            in
              do
                el "tbody" $ do
                  mapAccum rows $ \dynRows ->
                    let cells = (\(Row _ z) -> z) <$> dynRows
                    in
                      do
                        el "tr" $ do
                          mapAccum cells $ \dynCells ->
                            let blks = (\(Cell _ _ _ _ y) -> y) <$> dynCells
                            in
                              do
                                el "td" $ renderBlocks
                                  cfg
                                  (fmap (fmap blockToDSum) blks)
  DivTag :=> Compose dynxs ->
    let (attr, xs) = splitDynPure (runIdentity <$> dynxs)
    in  elPandocAttr "div" attr $ renderBlocks cfg xs
  NullTag :=> Compose _ -> blank >> pure mempty
 where
  renderInlinesCheckbox (0 :: Int) (StrTag :=> Compose dynV) =
    dynDyn
      $   (\case
            "☐" -> mempty <$ checkboxEl False
            "☒" -> mempty <$ checkboxEl True
            s   -> mempty <$ text s
          )
      .   runIdentity
      <$> dynV
  renderInlinesCheckbox _ is = renderInline cfg is


  checkboxEl checked = do
    let attrs = mconcat
          [ "type" =: "checkbox"
          , "disabled" =: "True"
          , bool mempty ("checked" =: "True") checked
          ]
    void $ elAttr "input" attrs blank

  startFrom :: Int -> Map Text Text
  startFrom idx = bool mempty ("start" =: T.pack (show idx)) (idx /= 1)
  listStyle :: ListNumberStyle -> Map Text Text
  listStyle = \case
    LowerRoman -> "type" =: "i"
    UpperRoman -> "type" =: "I"
    LowerAlpha -> "type" =: "a"
    UpperAlpha -> "type" =: "A"
    _          -> mempty

renderInlines
  :: (DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, Monoid a)
  => Config t m a
  -> Dynamic t [DSum InlineTag Identity]
  -> ReaderT (Dynamic t Footnotes) m (Dynamic t a)
renderInlines cfg xs = do
  mapAccum xs $ \x -> do
    x' <- factorDyn x
    dynDyn $ fmap (renderInline cfg) x'

renderInline
  :: (DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, Monoid a)
  => Config t m a
  -> DSum InlineTag (Compose (Dynamic t) Identity)
  -> ReaderT (Dynamic t Footnotes) m (Dynamic t a)
renderInline cfg = \case
  StrTag  :=> Compose x  -> dynText (runIdentity <$> x) >> pure mempty
  EmphTag :=> Compose xs -> el "em" $ renderInlines cfg (runIdentity <$> xs)
  StrongTag :=> Compose xs ->
    el "strong" $ renderInlines cfg (runIdentity <$> xs)
  UnderlineTag :=> Compose xs ->
    el "u" $ renderInlines cfg (runIdentity <$> xs)
  StrikeoutTag :=> Compose xs ->
    el "strike" $ renderInlines cfg (runIdentity <$> xs)
  SuperscriptTag :=> Compose xs ->
    el "sup" $ renderInlines cfg (runIdentity <$> xs)
  SubscriptTag :=> Compose xs ->
    el "sub" $ renderInlines cfg (runIdentity <$> xs)
  SmallCapsTag :=> Compose xs ->
    el "small" $ renderInlines cfg (runIdentity <$> xs)
  QuotedTag :=> Compose dynxs ->
    let (qt, xs) = splitDynPure (runIdentity <$> dynxs)
    in  dynText (leftQuote <$> qt) >> renderInlines cfg xs <* dynText
          (rightQuote <$> qt)
  CiteTag :=> _ -> do
    el "pre" $ text "error[reflex-doc-pandoc]: Pandoc Cite is not handled"
    pure mempty
  CodeTag :=> Compose dynxs ->
    let (attr, x) = splitDynPure (runIdentity <$> dynxs)
    in  elPandocAttr "code" attr $ do
          dynText x
          pure mempty
  SpaceTag     :=> _ -> text " " >> pure mempty
  SoftBreakTag :=> _ -> text " " >> pure mempty
  LineBreakTag :=> _ -> el "br" blank >> pure mempty
  RawInlineTag :=> Compose x ->
    lift
      $ _config_renderRaw cfg (uncurry PandocRawNode_Inline . runIdentity <$> x)
      >> pure mempty
  MathTag :=> Compose dynxs ->
    -- http://docs.mathjax.org/en/latest/basic/mathematics.html#tex-and-latex-input
    let (mathType, s) = splitDynPure (runIdentity <$> dynxs)
        mathTypeCls   = \case
          InlineMath  -> "math inline"
          DisplayMath -> "math display"
        mathDelimLeft = \case
          InlineMath  -> "\\("
          DisplayMath -> "$$"
        mathDelimRight = \case
          InlineMath  -> "\\)"
          DisplayMath -> "$$"
    in  elDynClass "span" (mathTypeCls <$> mathType) $ do
          dynText (mathDelimLeft <$> mathType)
          dynText s
          dynText (mathDelimRight <$> mathType)
          pure mempty
  LinkTag :=> Compose dynxs ->
    let (attr, xs, l)  = splitDyn3Pure (runIdentity <$> dynxs)
        (lUrl, lTitle) = splitDynPure l
    in  do
          let attrMap       = renderAttr <$> attr
              defaultRender = do
                let attr' =
                      fmap sansEmptyAttrs
                        $  attrMap
                        <> (("href" =:) <$> lUrl)
                        <> (("title" =:) <$> lTitle)
                elDynAttr "a" attr' $ renderInlines cfg xs
          fns <- ask
          lift $ _config_renderLink cfg
                                    (runReaderT defaultRender fns)
                                    lUrl
                                    (attrMap <> (("title" =:) <$> lTitle))
                                    xs
  ImageTag :=> Compose dynxs ->
    elDynAttr "img" (imageAttrs . runIdentity <$> dynxs) blank >> pure mempty
  NoteTag :=> Compose dynXs -> do
    dynFs :: Dynamic t Footnotes <- ask
    dynDyn
      $   (\xs fs -> case Map.lookup (mkFootnote xs) fs of
            Nothing ->
              -- No footnote in the global map (this means that the user has
              -- defined a footnote inside a footnote); just put the whole thing in
              -- aside.
                       elClass "aside" "footnote-inline"
              $ renderBlocks cfg (fmap blockToDSum . runIdentity <$> dynXs)
            Just idx -> renderFootnoteRef idx >> pure mempty
          )
      <$> (runIdentity <$> dynXs)
      <*> dynFs
  SpanTag :=> Compose dynxs ->
    let (attr, xs) = splitDynPure (runIdentity <$> dynxs)
    in  elPandocAttr "span" attr $ renderInlines cfg xs
 where

  leftQuote = \case
    SingleQuote -> ("‘" :: Text)
    DoubleQuote -> "“"

  rightQuote = \case
    SingleQuote -> ("’" :: Text)
    DoubleQuote -> "”"

  -- Pandoc stores Img's alt text as [Inline]
  imageAttrs (attr, imgInlines, (iUrl, iTitle)) =
    sansEmptyAttrs
      $  renderAttr attr
      <> ("src" =: iUrl <> "title" =: iTitle <> "alt" =: plainify imgInlines)

splitDyn3Pure
  :: Reflex t => Dynamic t (a, b, c) -> (Dynamic t a, Dynamic t b, Dynamic t c)
splitDyn3Pure dynxs =
  ( (\(x, _, _) -> x) <$> dynxs
  , (\(_, x, _) -> x) <$> dynxs
  , (\(_, _, x) -> x) <$> dynxs
  )
data InlineTag a where
  StrTag ::InlineTag Text -- ^ Text (string)
  EmphTag ::InlineTag [DSum InlineTag Identity] -- ^ Emphasized text (list of inlines)
  UnderlineTag ::InlineTag [DSum InlineTag Identity] -- ^ Underlined text (list of inlines)
  StrongTag ::InlineTag [DSum InlineTag Identity] -- ^ Strongly emphasized text (list of inlines)
  StrikeoutTag ::InlineTag [DSum InlineTag Identity] -- ^ Strikeout text (list of inlines)
  SuperscriptTag ::InlineTag [DSum InlineTag Identity] -- ^ Superscripted text (list of inlines)
  SubscriptTag ::InlineTag [DSum InlineTag Identity] -- ^ Subscripted text (list of inlines)
  SmallCapsTag ::InlineTag [DSum InlineTag Identity] -- ^ Small caps text (list of inlines)
  QuotedTag ::InlineTag (QuoteType, [DSum InlineTag Identity]) -- ^ Quoted text (list of inlines)
  CiteTag ::InlineTag ([Citation], [DSum InlineTag Identity]) -- ^ Citation (list of inlines)
  CodeTag ::InlineTag (Attr, Text) -- ^ Inline code (literal)
  SpaceTag ::InlineTag () -- ^ Inter-word space
  SoftBreakTag ::InlineTag () -- ^ Soft line break
  LineBreakTag ::InlineTag () -- ^ Hard line break
  MathTag ::InlineTag (MathType, Text) -- ^ TeX math (literal)
  RawInlineTag ::InlineTag (Format, Text) -- ^ Raw inline
  LinkTag ::InlineTag (Attr, [DSum InlineTag Identity], Target) -- ^ Hyperlink: alt text (list of inlines), target
  ImageTag ::InlineTag (Attr, [Inline], Target) -- ^ Image: alt text (list of inlines), target
  NoteTag ::InlineTag [Block] -- ^ Footnote or endnote
  SpanTag ::InlineTag (Attr, [DSum InlineTag Identity]) -- ^ Generic inline container with attributes

inlineToDSum :: Inline -> DSum InlineTag Identity
inlineToDSum = \case
  Str         x        -> StrTag ==> x
  Emph        xs       -> EmphTag ==> fmap inlineToDSum xs
  Strong      xs       -> StrongTag ==> fmap inlineToDSum xs
  Underline   xs       -> UnderlineTag ==> fmap inlineToDSum xs
  Strikeout   xs       -> StrikeoutTag ==> fmap inlineToDSum xs
  Superscript xs       -> SuperscriptTag ==> fmap inlineToDSum xs
  Subscript   xs       -> SubscriptTag ==> fmap inlineToDSum xs
  SmallCaps   xs       -> SmallCapsTag ==> fmap inlineToDSum xs
  Quoted qt   xs       -> QuotedTag ==> (qt, fmap inlineToDSum xs)
  Cite   ct   xs       -> CiteTag ==> (ct, fmap inlineToDSum xs)
  Code   attr x        -> CodeTag ==> (attr, x)
  Space                -> SpaceTag ==> ()
  SoftBreak            -> SoftBreakTag ==> ()
  LineBreak            -> LineBreakTag ==> ()
  RawInline fmt      x -> RawInlineTag ==> (fmt, x)
  Math      mathType s -> MathTag ==> (mathType, s)
  Link  attr xs target -> LinkTag ==> (attr, fmap inlineToDSum xs, target)
  Image attr xs target -> ImageTag ==> (attr, xs, target)
  Note xs              -> NoteTag ==> xs
  Span attr xs         -> SpanTag ==> (attr, fmap inlineToDSum xs)

instance GEq InlineTag where
  geq StrTag         StrTag         = Just Refl
  geq EmphTag        EmphTag        = Just Refl
  geq UnderlineTag   UnderlineTag   = Just Refl
  geq StrongTag      StrongTag      = Just Refl
  geq StrikeoutTag   StrikeoutTag   = Just Refl
  geq SuperscriptTag SuperscriptTag = Just Refl
  geq SubscriptTag   SubscriptTag   = Just Refl
  geq SmallCapsTag   SmallCapsTag   = Just Refl
  geq QuotedTag      QuotedTag      = Just Refl
  geq CiteTag        CiteTag        = Just Refl
  geq CodeTag        CodeTag        = Just Refl
  geq SpaceTag       SpaceTag       = Just Refl
  geq SoftBreakTag   SoftBreakTag   = Just Refl
  geq LineBreakTag   LineBreakTag   = Just Refl
  geq MathTag        MathTag        = Just Refl
  geq RawInlineTag   RawInlineTag   = Just Refl
  geq LinkTag        LinkTag        = Just Refl
  geq ImageTag       ImageTag       = Just Refl
  geq NoteTag        NoteTag        = Just Refl
  geq SpanTag        SpanTag        = Just Refl
  geq _              _              = Nothing

data BlockTag a where
  PlainTag ::BlockTag [DSum InlineTag Identity] -- ^ Plain text, not a paragraph
  ParaTag ::BlockTag [DSum InlineTag Identity] -- ^ Paragraph
  LineBlockTag ::BlockTag [[DSum InlineTag Identity]] -- ^ Multiple non-breaking lines
  CodeBlockTag ::BlockTag (Attr, Text) -- ^ Code block (literal) with attributes
  RawBlockTag ::BlockTag (Format, Text) -- ^ Raw block
  BlockQuoteTag ::BlockTag [DSum BlockTag Identity] -- ^ Block quote (list of blocks)
  OrderedListTag ::BlockTag (ListAttributes, [[DSum BlockTag Identity]]) -- ^ Ordered list (attributes and a list of items, each a list of blocks)
  BulletListTag ::BlockTag [[DSum BlockTag Identity]] -- ^ Bullet list (list of items, each a list of blocks)
  DefinitionListTag ::BlockTag [([DSum InlineTag Identity], [[DSum BlockTag Identity]])] -- ^ Definition list. Each list item is a pair consisting of a term (a list of inlines) and one or more definitions (each a list of blocks)
  HeaderTag ::BlockTag (Int, Attr, [DSum InlineTag Identity]) -- ^ Header - level (integer) and text (inlines)
  HorizontalRuleTag ::BlockTag () -- ^ Horizontal rule
  TableTag ::BlockTag (Attr, Caption, [ColSpec], TableHead, [TableBody], TableFoot) -- ^ Table, with attributes, caption, optional short caption, column alignments and widths (required), table head, table bodies, and table foot
  DivTag ::BlockTag (Attr, [DSum BlockTag Identity]) -- ^ Generic block container with attributes
  NullTag ::BlockTag () -- ^ Nothing


blockToDSum :: Block -> DSum BlockTag Identity
blockToDSum = \case
  Plain     xs     -> PlainTag ==> fmap inlineToDSum xs
  Para      xs     -> ParaTag ==> fmap inlineToDSum xs
  LineBlock xss    -> LineBlockTag ==> fmap (fmap inlineToDSum) xss
  CodeBlock attr x -> CodeBlockTag ==> (attr, x)
  RawBlock  fmt  x -> RawBlockTag ==> (fmt, x)
  BlockQuote xs    -> BlockQuoteTag ==> fmap blockToDSum xs
  OrderedList attrs xss ->
    OrderedListTag ==> (attrs, fmap (fmap blockToDSum) xss)
  BulletList xss -> BulletListTag ==> fmap (fmap blockToDSum) xss
  DefinitionList defs ->
    DefinitionListTag ==> fmap (bimap inlineToDSum (fmap blockToDSum)) defs
  Header level attr xs -> HeaderTag ==> (level, attr, fmap inlineToDSum xs)
  HorizontalRule       -> HorizontalRuleTag ==> ()
  Table attr captions colSpec tableHead tbodys tfoot ->
    TableTag ==> (attr, captions, colSpec, tableHead, tbodys, tfoot)
  Div attr xs -> DivTag ==> (attr, fmap blockToDSum xs)
  Null        -> NullTag ==> ()

instance GEq BlockTag where
  geq PlainTag          PlainTag          = Just Refl
  geq ParaTag           ParaTag           = Just Refl
  geq LineBlockTag      LineBlockTag      = Just Refl
  geq CodeBlockTag      CodeBlockTag      = Just Refl
  geq RawBlockTag       RawBlockTag       = Just Refl
  geq BlockQuoteTag     BlockQuoteTag     = Just Refl
  geq OrderedListTag    OrderedListTag    = Just Refl
  geq BulletListTag     BulletListTag     = Just Refl
  geq DefinitionListTag DefinitionListTag = Just Refl
  geq HeaderTag         HeaderTag         = Just Refl
  geq HorizontalRuleTag HorizontalRuleTag = Just Refl
  geq TableTag          TableTag          = Just Refl
  geq DivTag            DivTag            = Just Refl
  geq NullTag           NullTag           = Just Refl
  geq _                 _                 = Nothing

