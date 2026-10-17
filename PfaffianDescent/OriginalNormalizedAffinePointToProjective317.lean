import PfaffianDescent.OriginalNormalizedWholeOpenPoint317
import PfaffianDescent.OriginalNormalizedProjectiveTower317

/-! SOURCE ONLY317. The physical normalized finite-flat family pushes into the
SAME original projective hypersurface, with its whole ideal and rank retained.
Reduction compatibility follows from actual Cartesian chart diagrams. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Cast only the base projection, then use the accepted native finite-flat
push through an open. Closedness is derived by314 from finiteness over a
separated ambient base map; it is not required as an extra point premise. -/
private def physicalChartPointPush317
    {Y X T : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]
    (F : X ⟶ T) [IsSeparated F] (G : Y ⟶ T) (h : a ≫ F = G)
    (n : ℕ) (Q : FiniteFlatHilbertPoint195 G n) :
    FiniteFlatHilbertPoint195 F n :=
  nativeFiniteFlatPointPushOpen314 a F n
    (nativeFiniteFlatPointProjectionEq317 h.symm n Q)

private theorem physicalChartPointPush_wholeIdeal317
    {Y X T : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]
    (F : X ⟶ T) [IsSeparated F] (G : Y ⟶ T) (h : a ≫ F = G)
    (n : ℕ) (Q : FiniteFlatHilbertPoint195 G n) :
    (physicalChartPointPush317 a F G h n Q).val = Q.val.map a :=
  (nativeFiniteFlatPointPushOpen_wholeIdeal314 a F n
    (nativeFiniteFlatPointProjectionEq317 h.symm n Q)).trans
      (congrArg (fun J : Y.IdealSheafData => J.map a)
        (nativeFiniteFlatPointProjectionEq_wholeIdeal317 h.symm n Q))

/-- The actual finite composite is closed, even though the ambient chart
embedding is open. Proof dictionaries are derived from Q and separated F. -/
private theorem physicalChartFiniteComposite_isClosed317
    {Y X T : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]
    (F : X ⟶ T) [IsSeparated F] (G : Y ⟶ T) (h : a ≫ F = G)
    (n : ℕ) (Q : FiniteFlatHilbertPoint195 G n) :
    IsClosedImmersion (Q.val.subschemeι ≫ a) := by
  have hb : (Q.val.subschemeι ≫ a) ≫ F = Q.val.subschemeι ≫ G :=
    (Category.assoc _ _ _).trans (congrArg (fun t => Q.val.subschemeι ≫ t) h)
  letI : IsFinite ((Q.val.subschemeι ≫ a) ≫ F) := hb.symm ▸ Q.property.1
  exact nativeFiniteClosedThroughOpen_isClosed314 Q.val.subschemeι a F

private theorem physicalChartPointPush_range317
    {Y X T : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]
    (F : X ⟶ T) [IsSeparated F] (G : Y ⟶ T) (h : a ≫ F = G)
    (n : ℕ) (Q : FiniteFlatHilbertPoint195 G n) :
    Set.range (physicalChartPointPush317 a F G h n Q).val.subschemeι ⊆ Set.range a :=
  nativeFiniteFlatPointPushOpen_range315 a F n
    (nativeFiniteFlatPointProjectionEq317 h.symm n Q)

/-- Cancel the genuine Cartesian bottom square after replacing only native
projection equalities. This is proved before any original coefficient rings,
normalized chart algebras or projective scheme aliases are substituted. -/
private theorem physicalChartReduction_isPullback317
    {Y0 Y X0 X T0 T : Scheme.{u}}
    (v : Y0 ⟶ Y) (a0 : Y0 ⟶ X0) (a : Y ⟶ X) (w : X0 ⟶ X)
    (F0 : X0 ⟶ T0) (F : X ⟶ T) (G0 : Y0 ⟶ T0) (G : Y ⟶ T)
    (c : T0 ⟶ T) (h0 : a0 ≫ F0 = G0) (h : a ≫ F = G)
    (H : IsPullback v G0 G c) (HX : IsPullback w F0 F c)
    (ha : v ≫ a = a0 ≫ w) : IsPullback v a0 a w := by
  have Houter : IsPullback v (a0 ≫ F0) (a ≫ F) c := by
    rw [h0, h]
    exact H
  exact Houter.of_bot ha HX

/-- Whole-image/base-change law, with closedness of the ACTUAL finite family
composite derived internally. The scalar-point reduction equality is an
abstract input here and is supplied by genuine195 base change in the caller. -/
private theorem physicalChartPointPush_wholeReduction317
    {Y0 Y X0 X T0 T : Scheme.{u}}
    (a0 : Y0 ⟶ X0) [IsOpenImmersion a0]
    (a : Y ⟶ X) [IsOpenImmersion a]
    (F0 : X0 ⟶ T0) [IsSeparated F0] (F : X ⟶ T) [IsSeparated F]
    (G0 : Y0 ⟶ T0) (G : Y ⟶ T) (h0 : a0 ≫ F0 = G0) (h : a ≫ F = G)
    (v : Y0 ⟶ Y) (w : X0 ⟶ X) (H : IsPullback v a0 a w)
    (n : ℕ) (Q0 : FiniteFlatHilbertPoint195 G0 n) (Q : FiniteFlatHilbertPoint195 G n)
    (hQ : Q0.val = Q.val.comap v) :
    (physicalChartPointPush317 a0 F0 G0 h0 n Q0).val =
      (physicalChartPointPush317 a F G h n Q).val.comap w := by
  letI : IsClosedImmersion (Q.val.subschemeι ≫ a) :=
    physicalChartFiniteComposite_isClosed317 a F G h n Q
  exact (physicalChartPointPush_wholeIdeal317 a0 F0 G0 h0 n Q0).trans
    ((congrArg (fun J : Y0.IdealSheafData => J.map a0) hQ).trans
      ((nativeEmbeddedIdealMapComap315 v a0 a w H Q.val).trans
        (congrArg (fun J : X.IdealSheafData => J.comap w)
          (physicalChartPointPush_wholeIdeal317 a F G h n Q).symm)))

variable {B : Type u} [CommRing B] (r : MvPolynomial (Fin 4) B)
variable {d : ℕ} (hr : r.IsHomogeneous d) (j : Fin 4) (n : ℕ)
variable (Q : FiniteFlatHilbertPoint195
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j)))) n)

/-- Push the physical normalized finite-flat family into the ORIGINAL
projective hypersurface over B. Same rank n; no supplied projective family,
closedness, properness or comparison certificate is needed. -/
def originalNormalizedAffinePointToProjective317 :
    FiniteFlatHilbertPoint195 (hypersurfaceToBase r hr) n :=
  @physicalChartPointPush317
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (hypersurface r hr) (Spec (.of B))
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j)
    (hypersurfaceToBase r hr) (originalNormalizedWholeOpen_separated317 r hr)
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j) n Q

/-- The physical WHOLE mapped ideal, including nilpotent structure. -/
lemma originalNormalizedAffinePointToProjective_wholeIdeal317 :
    (originalNormalizedAffinePointToProjective317 r hr j n Q).val =
      Q.val.map (originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
  @physicalChartPointPush_wholeIdeal317
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (hypersurface r hr) (Spec (.of B))
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j)
    (hypersurfaceToBase r hr) (originalNormalizedWholeOpen_separated317 r hr)
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j) n Q

/-- The SAME normalized whole family's composite immersion is closed in
the original projective hypersurface, derived from finite/proper and separated
facts already proved. This is not an added outcome assumption. -/
lemma originalNormalizedAffinePointToProjective_isClosed317 :
    IsClosedImmersion (Q.val.subschemeι ≫
      originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
  @physicalChartFiniteComposite_isClosed317
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (hypersurface r hr) (Spec (.of B))
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j)
    (hypersurfaceToBase r hr) (originalNormalizedWholeOpen_separated317 r hr)
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j) n Q

/-- The entire pushed family is contained in the actual original chart. -/
lemma originalNormalizedAffinePointToProjective_range317 :
    Set.range (originalNormalizedAffinePointToProjective317 r hr j n Q).val.subschemeι ⊆
      Set.range (originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
  @physicalChartPointPush_range317
    (Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 r j)))
    (hypersurface r hr) (Spec (.of B))
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j)
    (hypersurfaceToBase r hr) (originalNormalizedWholeOpen_separated317 r hr)
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j) n Q

variable {S : Type u} [CommRing S] (c : B →+* S)
variable (s : MvPolynomial (Fin 4) S) (hs : s.IsHomogeneous d) (he : r.map c = s)

/-- The actual normalized embeddings form a Cartesian square under the
specified ORIGINAL projective equation reduction. The target polynomial s
is kept literally, with the original equality r.map c = s. -/
lemma originalNormalizedChartEmbedding_reduction_isPullback317 :
    IsPullback (originalNormalizedProjectiveReductionOfEquation317 c r hr s hs he j)
      (originalNormalizedHypersurfaceChartEmbedding312 s hs j)
      (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
      (hypersurfaceReductionMap c r hr s hs he) :=
  physicalChartReduction_isPullback317
    (originalNormalizedProjectiveReductionOfEquation317 c r hr s hs he j)
    (originalNormalizedHypersurfaceChartEmbedding312 s hs j)
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (hypersurfaceReductionMap c r hr s hs he)
    (hypersurfaceToBase s hs) (hypersurfaceToBase r hr)
    (Spec.map (CommRingCat.ofHom (R := S)
      (S := OriginalNormalizedHypersurfaceAlgebra312 s j)
      (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 s j))))
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (Spec.map (CommRingCat.ofHom c))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 s hs j)
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j)
    (originalNormalizedProjectiveReductionOfEquation_isPullback317 c r hr s hs he j)
    (isPullback_hypersurfaceReductionMap c r hr s hs he)
    (originalNormalizedProjectiveReductionOfEquation_toOriginal317 c r hr s hs he j)

/-- Pushing the GENUINE195 physical normalized reduction agrees on whole
ideals with reducing the original projective whole family. Every comparison
hypothesis is derived; no reduced/projective family is supplied as outcome. -/
lemma originalNormalizedAffinePointToProjective_reductionWholeIdeal317 :
    (originalNormalizedAffinePointToProjective317 s hs j n
      (finiteFlatHilbertBaseChange195
        (originalNormalizedProjectiveReductionOfEquation317 c r hr s hs he j)
        (Spec.map (CommRingCat.ofHom (R := S)
          (S := OriginalNormalizedHypersurfaceAlgebra312 s j)
          (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 s j))))
        (Spec.map (CommRingCat.ofHom (R := B)
          (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
          (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
        (Spec.map (CommRingCat.ofHom c))
        (originalNormalizedProjectiveReductionOfEquation_isPullback317 c r hr s hs he j) n Q)).val =
      (originalNormalizedAffinePointToProjective317 r hr j n Q).val.comap
        (hypersurfaceReductionMap c r hr s hs he) := by
  letI : IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 s hs j) :=
    originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 s hs j
  letI : IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 r hr j) :=
    originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312 r hr j
  letI : IsSeparated (hypersurfaceToBase s hs) := originalNormalizedWholeOpen_separated317 s hs
  letI : IsSeparated (hypersurfaceToBase r hr) := originalNormalizedWholeOpen_separated317 r hr
  exact physicalChartPointPush_wholeReduction317
    (originalNormalizedHypersurfaceChartEmbedding312 s hs j)
    (originalNormalizedHypersurfaceChartEmbedding312 r hr j)
    (hypersurfaceToBase s hs) (hypersurfaceToBase r hr)
    (Spec.map (CommRingCat.ofHom (R := S)
      (S := OriginalNormalizedHypersurfaceAlgebra312 s j)
      (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 s j))))
    (Spec.map (CommRingCat.ofHom (R := B)
      (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
      (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 s hs j)
    (originalNormalizedHypersurfaceChartEmbedding_toBase312 r hr j)
    (originalNormalizedProjectiveReductionOfEquation317 c r hr s hs he j)
    (hypersurfaceReductionMap c r hr s hs he)
    (originalNormalizedChartEmbedding_reduction_isPullback317 r hr j c s hs he) n
    (finiteFlatHilbertBaseChange195
        (originalNormalizedProjectiveReductionOfEquation317 c r hr s hs he j)
        (Spec.map (CommRingCat.ofHom (R := S)
          (S := OriginalNormalizedHypersurfaceAlgebra312 s j)
          (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 s j))))
        (Spec.map (CommRingCat.ofHom (R := B)
          (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
          (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
        (Spec.map (CommRingCat.ofHom c))
        (originalNormalizedProjectiveReductionOfEquation_isPullback317 c r hr s hs he j) n Q) Q
    (finiteFlatHilbertBaseChange195_ideal
      (originalNormalizedProjectiveReductionOfEquation317 c r hr s hs he j)
      (Spec.map (CommRingCat.ofHom (R := S)
        (S := OriginalNormalizedHypersurfaceAlgebra312 s j)
        (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 s j))))
      (Spec.map (CommRingCat.ofHom (R := B)
        (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
        (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
      (Spec.map (CommRingCat.ofHom c))
      (originalNormalizedProjectiveReductionOfEquation_isPullback317 c r hr s hs he j) n Q)

/-- Equality as actual rank-n finite-flat points, not only support or a scalar
coefficient classifier. Target is the same specified original hypersurface. -/
lemma originalNormalizedAffinePointToProjective_reduction317 :
    originalNormalizedAffinePointToProjective317 s hs j n
      (finiteFlatHilbertBaseChange195
        (originalNormalizedProjectiveReductionOfEquation317 c r hr s hs he j)
        (Spec.map (CommRingCat.ofHom (R := S)
          (S := OriginalNormalizedHypersurfaceAlgebra312 s j)
          (algebraMap S (OriginalNormalizedHypersurfaceAlgebra312 s j))))
        (Spec.map (CommRingCat.ofHom (R := B)
          (S := OriginalNormalizedHypersurfaceAlgebra312 r j)
          (algebraMap B (OriginalNormalizedHypersurfaceAlgebra312 r j))))
        (Spec.map (CommRingCat.ofHom c))
        (originalNormalizedProjectiveReductionOfEquation_isPullback317 c r hr s hs he j) n Q) =
      finiteFlatHilbertBaseChange195
        (hypersurfaceReductionMap c r hr s hs he)
        (hypersurfaceToBase s hs) (hypersurfaceToBase r hr)
        (Spec.map (CommRingCat.ofHom c))
        (isPullback_hypersurfaceReductionMap c r hr s hs he) n
        (originalNormalizedAffinePointToProjective317 r hr j n Q) := by
  apply Subtype.ext
  exact (originalNormalizedAffinePointToProjective_reductionWholeIdeal317
    r hr j n Q c s hs he).trans
      (finiteFlatHilbertBaseChange195_ideal
        (hypersurfaceReductionMap c r hr s hs he)
        (hypersurfaceToBase s hs) (hypersurfaceToBase r hr)
        (Spec.map (CommRingCat.ofHom c))
        (isPullback_hypersurfaceReductionMap c r hr s hs he) n
        (originalNormalizedAffinePointToProjective317 r hr j n Q)).symm

end PfaffianDescent
end
