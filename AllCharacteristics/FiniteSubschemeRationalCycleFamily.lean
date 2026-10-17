import AllCharacteristics.FiniteSubschemeFunctor
import AllCharacteristics.FiniteSubschemeRank
import PfaffianDescent.FiniteSchemeFundamentalIso
import PfaffianDescent.CurveFamilyCycleQuotient
import PfaffianDescent.ProjectiveLineSmooth

/-!
# Rational cycle families from finite-subscheme data

An ideal-defined finite-flat subscheme of the pullback of a scheme over the
projective line is already the finite-flat family used to generate rational
zero-cycle relations.  This records that conversion without choosing a
configuration-space presentation.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AllCharacteristics

universe u

/-- A finite subscheme can be pulled back constantly along the projective
line.  This is the literal product family over the parameter line; moving
families for Voisin's argument will use the same ambient Cartesian square
with a nonconstant ideal. -/
noncomputable def constantLineFiniteSubschemeDatum
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (n : ℕ) (D : FiniteSubschemeDatum f n) :
    FiniteSubschemeDatum (PfaffianDescent.projectiveLineAmbientToLine K f) n :=
  FiniteSubschemeDatum.baseChange
    (PfaffianDescent.projectiveLineAmbientToScheme K f)
    (PfaffianDescent.projectiveLineProjToBase K)
    (PfaffianDescent.projectiveLineAmbientIsPullback K f) D

/-- The constant projective-line family is defined by the pullback of the
original ideal along projection to the ambient scheme. -/
theorem constantLineFiniteSubschemeDatum_ideal
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (n : ℕ) (D : FiniteSubschemeDatum f n) :
    (constantLineFiniteSubschemeDatum f n D).val = D.val.comap
      (PfaffianDescent.projectiveLineAmbientToScheme K f) :=
  FiniteSubschemeDatum.baseChange_ideal
    (PfaffianDescent.projectiveLineAmbientToScheme K f)
    (PfaffianDescent.projectiveLineProjToBase K)
    (PfaffianDescent.projectiveLineAmbientIsPullback K f) D

/-- A rank-`n` finite-subscheme datum in the projective-line pullback of `f`
gives a rational cycle family on `X`. -/
noncomputable def rationalCycleFamily_of_finiteSubschemeDatum
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n) :
    PfaffianDescent.RationalCycleFamily f := by
  let toLine : D.val.subscheme ⟶ PfaffianDescent.projectiveLineProj K :=
    D.val.subschemeι ≫ pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)
  let toScheme : D.val.subscheme ⟶ X :=
    D.val.subschemeι ≫ pullback.fst f (PfaffianDescent.projectiveLineProjToBase K)
  have hover : toScheme ≫ f =
      toLine ≫ PfaffianDescent.projectiveLineProjToBase K := by
    dsimp [toScheme, toLine]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact
    { curve := D.val.subscheme
      toLine := toLine
      finite := D.property.1
      flat := D.property.2.1
      finitelyPresented := D.property.2.2.1
      toScheme := toScheme
      overBase := hover }

/-- The fiber of `X × ℙ¹` over either distinguished point is canonically
isomorphic to `X`. -/
noncomputable def lineFiberAmbientIso
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (b : Bool) : X ≅
      pullback (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K))
        (PfaffianDescent.projectiveLineEndpoint K b) := by
  let l := PfaffianDescent.projectiveLineProjToBase K
  let e := PfaffianDescent.projectiveLineEndpoint K b
  let r : pullback f (e ≫ l) ≅ pullback f (𝟙 _) :=
    pullback.congrHom rfl (PfaffianDescent.projectiveLineEndpoint_toBase K b)
  let j : pullback f (𝟙 _) ≅ X := asIso (pullback.fst f (𝟙 _))
  exact j.symm ≪≫ r.symm ≪≫ (pullbackLeftPullbackSndIso f l e).symm

/-- The map from `X` into `X × ℙ¹` that realizes the indicated endpoint
fiber. -/
noncomputable def lineFiberAmbientMap
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (b : Bool) : X ⟶ pullback f (PfaffianDescent.projectiveLineProjToBase K) :=
  (lineFiberAmbientIso f b).hom ≫
    pullback.fst (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K))
      (PfaffianDescent.projectiveLineEndpoint K b)

lemma lineFiberAmbientMap_fst
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (b : Bool) :
    lineFiberAmbientMap f b ≫ pullback.fst f (PfaffianDescent.projectiveLineProjToBase K) =
      𝟙 X := by
  let l := PfaffianDescent.projectiveLineProjToBase K
  let e := PfaffianDescent.projectiveLineEndpoint K b
  let r : pullback f (e ≫ l) ≅ pullback f (𝟙 _) :=
    pullback.congrHom rfl (PfaffianDescent.projectiveLineEndpoint_toBase K b)
  let j : pullback f (𝟙 _) ≅ X := asIso (pullback.fst f (𝟙 _))
  let a := pullbackLeftPullbackSndIso f l e
  have hr : r.inv ≫ pullback.fst f (e ≫ l) = pullback.fst f (𝟙 _) := by
    apply (cancel_epi r.hom).1
    rw [Iso.hom_inv_id_assoc]
    dsimp [r, pullback.congrHom, pullback.map, asIso]
    rw [pullback.lift_fst]
    dsimp [l, e]
    simp
  have hj : j.inv ≫ pullback.fst f (𝟙 _) = 𝟙 X := by
    exact j.inv_hom_id
  change (j.symm ≪≫ r.symm ≪≫ a.symm).hom ≫
    pullback.fst (pullback.snd f l) e ≫ pullback.fst f l = 𝟙 X
  dsimp
  simp only [Category.assoc]
  rw [pullbackLeftPullbackSndIso_inv_fst, hr, hj]

lemma lineFiberAmbientIso_hom_snd
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (b : Bool) :
    (lineFiberAmbientIso f b).hom ≫
      pullback.snd (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K))
        (PfaffianDescent.projectiveLineEndpoint K b) = f := by
  let l := PfaffianDescent.projectiveLineProjToBase K
  let e := PfaffianDescent.projectiveLineEndpoint K b
  let r : pullback f (e ≫ l) ≅ pullback f (𝟙 _) :=
    pullback.congrHom rfl (PfaffianDescent.projectiveLineEndpoint_toBase K b)
  let j : pullback f (𝟙 _) ≅ X := asIso (pullback.fst f (𝟙 _))
  let a := pullbackLeftPullbackSndIso f l e
  have hr : r.inv ≫ pullback.snd f (e ≫ l) = pullback.snd f (𝟙 _) := by
    apply (cancel_epi r.hom).1
    rw [Iso.hom_inv_id_assoc]
    dsimp [r, pullback.congrHom, pullback.map, asIso]
    rw [pullback.lift_snd]
    dsimp [l, e]
    simp
  have hj : j.inv ≫ pullback.snd f (𝟙 _) = f := by
    apply (cancel_epi j.hom).1
    rw [Iso.hom_inv_id_assoc]
    dsimp [j, asIso]
    exact (pullback.condition (f := f) (g := 𝟙 _)).symm
  change (j.symm ≪≫ r.symm ≪≫ a.symm).hom ≫
    pullback.snd (pullback.snd f l) e = f
  dsimp
  simp only [Category.assoc]
  rw [pullbackLeftPullbackSndIso_inv_snd_snd, hr, hj]

lemma lineFiberAmbientIso_inv
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (b : Bool) :
    (lineFiberAmbientIso f b).inv =
      pullback.fst (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K))
        (PfaffianDescent.projectiveLineEndpoint K b) ≫
      pullback.fst f (PfaffianDescent.projectiveLineProjToBase K) := by
  apply (cancel_epi (lineFiberAmbientIso f b).hom).1
  rw [Iso.hom_inv_id]
  change 𝟙 X = lineFiberAmbientMap f b ≫
    pullback.fst f (PfaffianDescent.projectiveLineProjToBase K)
  rw [lineFiberAmbientMap_fst]

/-- The endpoint map gives a Cartesian square with the projective-line
family. -/
theorem lineFiberAmbientIsPullback
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (b : Bool) :
    IsPullback (lineFiberAmbientMap f b) f
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K))
      (PfaffianDescent.projectiveLineEndpoint K b) := by
  let i := lineFiberAmbientIso f b
  apply IsPullback.of_iso_pullback
    (i := i)
  · exact CommSq.mk (by
      dsimp [lineFiberAmbientMap]
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc, lineFiberAmbientIso_hom_snd])
  · rfl
  · simpa [i] using lineFiberAmbientIso_hom_snd f b

/-- Pulling a finite-subscheme family back to zero or infinity gives an
actual finite-subscheme datum on the original scheme. -/
noncomputable def finiteSubschemeDatumAtLineEndpoint
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n)
    (b : Bool) : FiniteSubschemeDatum f n :=
  FiniteSubschemeDatum.baseChange (lineFiberAmbientMap f b)
    (PfaffianDescent.projectiveLineEndpoint K b) (lineFiberAmbientIsPullback f b) D

/-- Étaleness of a finite subscheme over the projective-line parameter
restricts to either marked fiber.  Thus finite étale pencils retain reduced
endpoint data as well as the finite-flat structure used for their cycle
classes. -/
theorem etale_finiteSubschemeDatumAtLineEndpoint_toBase
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n)
    (b : Bool)
    (hEtale : Etale (D.val.subschemeι ≫
      pullback.snd f (PfaffianDescent.projectiveLineProjToBase K))) :
    Etale ((finiteSubschemeDatumAtLineEndpoint f n D b).val.subschemeι ≫ f) := by
  let a := lineFiberAmbientMap f b
  let e := PfaffianDescent.projectiveLineEndpoint K b
  let q := pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)
  let h : IsPullback a f q e := lineFiberAmbientIsPullback f b
  change Etale ((FiniteSubschemeDatum.baseChange a e h D).val.subschemeι ≫ f)
  exact MorphismProperty.of_isPullback (P := @Etale.{u})
    (isPullback_idealSubschemeFamily D.val a f q e h)
    (by simpa [q] using hEtale)

/-- An isomorphism of finite-subscheme data over the base transports
étaleness.  This lets endpoint identifications retain the reduced finite
geometry supplied by a configuration curve. -/
theorem etale_finiteSubschemeDatum_of_iso_over
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (D E : FiniteSubschemeDatum f n)
    (e : D.val.subscheme ≅ E.val.subscheme)
    (he : e.hom ≫ E.val.subschemeι = D.val.subschemeι)
    (hEtale : Etale (D.val.subschemeι ≫ f)) :
    Etale (E.val.subschemeι ≫ f) := by
  have hsub : E.val.subschemeι = e.inv ≫ D.val.subschemeι := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [hsub, Category.assoc]
  letI : MorphismProperty.RespectsIso @Etale := by
    rw [HasRingHomProperty.eq_affineLocally @Etale]
    exact affineLocally_respectsIso RingHom.Etale RingHom.Etale.respectsIso
  letI : MorphismProperty.ContainsIdentities @Etale :=
    HasRingHomProperty.containsIdentities (P := @Etale) RingHom.Etale.containsIdentities
  letI : Etale e.inv := MorphismProperty.of_isIso @Etale e.inv
  letI : Etale (D.val.subschemeι ≫ f) := hEtale
  infer_instance

/-- The literal fiber of the rational-cycle family is isomorphic to the
ideal-defined finite subscheme obtained by base change to that endpoint. -/
noncomputable def finiteSubschemeDatumAtLineEndpointFiberIso
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n)
    (b : Bool) :
    (rationalCycleFamily_of_finiteSubschemeDatum f n D).fiber b ≅
      (finiteSubschemeDatumAtLineEndpoint f n D b).val.subscheme := by
  let l := PfaffianDescent.projectiveLineProjToBase K
  let e := PfaffianDescent.projectiveLineEndpoint K b
  let q := pullback.snd f l
  let i := lineFiberAmbientIso f b
  let g := lineFiberAmbientMap f b
  let a : pullback D.val.subschemeι (pullback.fst q e) ≅
      pullback (D.val.subschemeι ≫ q) e :=
    pullbackRightPullbackFstIso q e D.val.subschemeι
  let k : pullback D.val.subschemeι g ⟶
      pullback D.val.subschemeι (pullback.fst q e) :=
    pullback.map D.val.subschemeι g D.val.subschemeι (pullback.fst q e)
      (𝟙 _) i.hom (𝟙 _) (by simp) (by rfl)
  haveI : IsIso k := by
    dsimp [k]
    exact @pullback.map_isIso _ _ _ _ _ _ _ _
      D.val.subschemeι g _ D.val.subschemeι (pullback.fst q e) _
      (𝟙 _) i.hom (𝟙 _) (by simp) (by rfl)
      (by infer_instance) (by infer_instance) (by infer_instance)
  exact a.symm ≪≫ (asIso k).symm ≪≫ pullbackSymmetry D.val.subschemeι g ≪≫
    (D.val.comapIso g).symm

/-- The endpoint-fiber isomorphism is over the original scheme. -/
theorem finiteSubschemeDatumAtLineEndpointFiberIso_hom_subschemeι
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n)
    (b : Bool) :
    (finiteSubschemeDatumAtLineEndpointFiberIso f n D b).hom ≫
      (finiteSubschemeDatumAtLineEndpoint f n D b).val.subschemeι =
      (rationalCycleFamily_of_finiteSubschemeDatum f n D).fiberToScheme b := by
  let l := PfaffianDescent.projectiveLineProjToBase K
  let e := PfaffianDescent.projectiveLineEndpoint K b
  let q := pullback.snd f l
  let i := lineFiberAmbientIso f b
  let g := lineFiberAmbientMap f b
  let a : pullback D.val.subschemeι (pullback.fst q e) ≅
      pullback (D.val.subschemeι ≫ q) e :=
    pullbackRightPullbackFstIso q e D.val.subschemeι
  let k : pullback D.val.subschemeι g ⟶
      pullback D.val.subschemeι (pullback.fst q e) :=
    pullback.map D.val.subschemeι g D.val.subschemeι (pullback.fst q e)
      (𝟙 _) i.hom (𝟙 _) (by simp) (by rfl)
  haveI : IsIso k := by
    dsimp [k]
    exact @pullback.map_isIso _ _ _ _ _ _ _ _
      D.val.subschemeι g _ D.val.subschemeι (pullback.fst q e) _
      (𝟙 _) i.hom (𝟙 _) (by simp) (by rfl)
      (by infer_instance) (by infer_instance) (by infer_instance)
  change (a.symm ≪≫ (asIso k).symm ≪≫ pullbackSymmetry D.val.subschemeι g ≪≫
    (D.val.comapIso g).symm).hom ≫ (D.val.comap g).subschemeι =
    pullback.fst (D.val.subschemeι ≫ q) e ≫ D.val.subschemeι ≫ pullback.fst f l
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [D.val.comapIso_inv_subschemeι]
  rw [pullbackSymmetry_hom_comp_fst]
  have hksnd : k ≫ pullback.snd D.val.subschemeι (pullback.fst q e) =
      pullback.snd D.val.subschemeι g ≫ i.hom := by
    dsimp [k]
    rw [pullback.lift_snd]
  have hk : (asIso k).inv ≫ pullback.snd D.val.subschemeι g =
      pullback.snd D.val.subschemeι (pullback.fst q e) ≫ i.inv := by
    apply (cancel_epi (asIso k).hom).1
    rw [Iso.hom_inv_id_assoc]
    change pullback.snd D.val.subschemeι g =
      k ≫ pullback.snd D.val.subschemeι (pullback.fst q e) ≫ i.inv
    rw [← Category.assoc, hksnd]
    simp only [Category.assoc, i.hom_inv_id, Category.comp_id]
  rw [hk]
  rw [show i.inv = pullback.fst q e ≫ pullback.fst f l by
    simpa [i, q, e, l] using lineFiberAmbientIso_inv f b]
  simpa [a, Category.assoc] using congrArg
    (fun t ↦ t ≫ pullback.fst f l)
    (pullbackRightPullbackFstIso_inv_snd_fst q e D.val.subschemeι)

/-- The fibers of the family attached to a finite-subscheme datum retain its
specified constant rank. -/
theorem rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_degree
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n)
    (b : Bool) :
    EffectiveZeroCycle.degree f
        ((rationalCycleFamily_of_finiteSubschemeDatum f n D).fiberCycle b) = n := by
  rw [PfaffianDescent.RationalCycleFamily.fiberCycle_degree]
  exact D.property.2.2.2
    (PfaffianDescent.projectiveLineEndpoint K b (IsLocalRing.closedPoint K))

/-- If a fiber of the finite-subscheme family is identified over the ambient
scheme with a second finite-subscheme datum, then its family cycle is exactly
that datum's canonical cycle.  This retains all local multiplicities at the
endpoint and is the endpoint bridge needed by a pencil of residual
subschemes. -/
lemma rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_datumCycle
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n)
    (b : Bool) (E : FiniteSubschemeDatum f n)
    (e : (rationalCycleFamily_of_finiteSubschemeDatum f n D).fiber b ≅ E.val.subscheme)
    (hmap : e.hom ≫ E.val.subschemeι =
      (rationalCycleFamily_of_finiteSubschemeDatum f n D).fiberToScheme b) :
    (rationalCycleFamily_of_finiteSubschemeDatum f n D).fiberCycle b =
      finiteSubschemeDatumCycle f E := by
  let F := rationalCycleFamily_of_finiteSubschemeDatum f n D
  letI : IsFinite (E.val.subschemeι ≫ f) := E.property.1
  letI : IsFinite E.val.subschemeι := IsFinite.of_comp _ f
  have hbase : e.hom ≫ (E.val.subschemeι ≫ f) =
      pullback.snd F.toLine (PfaffianDescent.projectiveLineEndpoint K b) := by
    rw [← Category.assoc, hmap, F.fiberToScheme_toBase]
  have h := PfaffianDescent.fiberCycle_eq_pushforward_of_iso f F b e
    E.val.subschemeι (E.val.subschemeι ≫ f) hmap hbase
  rw [h]
  rfl

/-- The endpoint cycle of an ideal-defined family is the canonical cycle of
its literal ideal-theoretic base change to that endpoint. -/
theorem rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_endpointDatumCycle
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n)
    (b : Bool) :
    (rationalCycleFamily_of_finiteSubschemeDatum f n D).fiberCycle b =
      finiteSubschemeDatumCycle f (finiteSubschemeDatumAtLineEndpoint f n D b) := by
  exact rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_datumCycle
    f n D b (finiteSubschemeDatumAtLineEndpoint f n D b)
    (finiteSubschemeDatumAtLineEndpointFiberIso f n D b)
    (finiteSubschemeDatumAtLineEndpointFiberIso_hom_subschemeι f n D b)

/-- The two actual endpoint data of a finite-subscheme family are rationally
equivalent in the quotient generated by finite-flat curve families. -/
theorem finiteSubschemeDatumAtLineEndpoint_cycleClass_eq
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n) :
    PfaffianDescent.curveFamilyCycleClass f
      (finiteSubschemeDatumCycle f
        (finiteSubschemeDatumAtLineEndpoint f n D false)).toZeroCycle =
      PfaffianDescent.curveFamilyCycleClass f
        (finiteSubschemeDatumCycle f
          (finiteSubschemeDatumAtLineEndpoint f n D true)).toZeroCycle := by
  rw [← rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_endpointDatumCycle f n D false,
    ← rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_endpointDatumCycle f n D true]
  exact PfaffianDescent.curveFamilyCycleClass_fibers f
    (rationalCycleFamily_of_finiteSubschemeDatum f n D)

/-- A finite-flat pencil of ideal-defined subschemes, together with
scheme-level identifications of its zero and infinity fibers.  This is the
form supplied by a Hilbert-scheme or complete-intersection construction;
the cycle equalities are consequences rather than extra hypotheses. -/
structure FiniteSubschemeDatumPencil
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ) (zeroDatum infinityDatum : FiniteSubschemeDatum f n) where
  datum : FiniteSubschemeDatum
    (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n
  zeroIso : (rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiber false ≅
    zeroDatum.val.subscheme
  zero_over : zeroIso.hom ≫ zeroDatum.val.subschemeι =
    (rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiberToScheme false
  infinityIso : (rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiber true ≅
    infinityDatum.val.subscheme
  infinity_over : infinityIso.hom ≫ infinityDatum.val.subschemeι =
    (rationalCycleFamily_of_finiteSubschemeDatum f n datum).fiberToScheme true

/-- Every ideal-defined finite-flat family determines a pencil whose endpoint
data are its actual ideal-theoretic base changes. -/
noncomputable def FiniteSubschemeDatumPencil.ofDatum
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ)
    (D : FiniteSubschemeDatum
      (pullback.snd f (PfaffianDescent.projectiveLineProjToBase K)) n) :
    FiniteSubschemeDatumPencil f n
      (finiteSubschemeDatumAtLineEndpoint f n D false)
      (finiteSubschemeDatumAtLineEndpoint f n D true) where
  datum := D
  zeroIso := finiteSubschemeDatumAtLineEndpointFiberIso f n D false
  zero_over := finiteSubschemeDatumAtLineEndpointFiberIso_hom_subschemeι f n D false
  infinityIso := finiteSubschemeDatumAtLineEndpointFiberIso f n D true
  infinity_over := finiteSubschemeDatumAtLineEndpointFiberIso_hom_subschemeι f n D true

/-- The constant product of a finite subscheme with the parameter line,
viewed as a finite-flat pencil with its literal endpoint data. -/
noncomputable def constantLineFiniteSubschemeDatumPencil
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ) (D : FiniteSubschemeDatum f n) :
    FiniteSubschemeDatumPencil f n
      (finiteSubschemeDatumAtLineEndpoint f n
        (constantLineFiniteSubschemeDatum f n D) false)
      (finiteSubschemeDatumAtLineEndpoint f n
        (constantLineFiniteSubschemeDatum f n D) true) :=
  FiniteSubschemeDatumPencil.ofDatum f n (constantLineFiniteSubschemeDatum f n D)

/-- Retarget a finite-subscheme pencil along isomorphisms of its endpoint
subschemes over the ambient scheme.  Complete-intersection and configuration
constructions usually identify the endpoint schemes in this form, rather than
by definitional equality of their ideal presentations. -/
noncomputable def FiniteSubschemeDatumPencil.retarget
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {n : ℕ} {zeroDatum infinityDatum : FiniteSubschemeDatum f n}
    (P : FiniteSubschemeDatumPencil f n zeroDatum infinityDatum)
    (zeroDatum' infinityDatum' : FiniteSubschemeDatum f n)
    (zeroIso : zeroDatum.val.subscheme ≅ zeroDatum'.val.subscheme)
    (zero_over : zeroIso.hom ≫ zeroDatum'.val.subschemeι = zeroDatum.val.subschemeι)
    (infinityIso : infinityDatum.val.subscheme ≅ infinityDatum'.val.subscheme)
    (infinity_over : infinityIso.hom ≫ infinityDatum'.val.subschemeι =
      infinityDatum.val.subschemeι) :
    FiniteSubschemeDatumPencil f n zeroDatum' infinityDatum' where
  datum := P.datum
  zeroIso := P.zeroIso ≪≫ zeroIso
  zero_over := by
    rw [Iso.trans_hom, Category.assoc, zero_over, P.zero_over]
  infinityIso := P.infinityIso ≪≫ infinityIso
  infinity_over := by
    rw [Iso.trans_hom, Category.assoc, infinity_over, P.infinity_over]

/-- The rational-cycle family underlying a finite-subscheme pencil. -/
noncomputable def FiniteSubschemeDatumPencil.toRationalCycleFamily
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {n : ℕ} {zeroDatum infinityDatum : FiniteSubschemeDatum f n}
    (P : FiniteSubschemeDatumPencil f n zeroDatum infinityDatum) :
    PfaffianDescent.RationalCycleFamily f :=
  rationalCycleFamily_of_finiteSubschemeDatum f n P.datum

/-- The zero endpoint of a finite-subscheme pencil carries exactly the
canonical cycle of its specified zero datum. -/
theorem FiniteSubschemeDatumPencil.fiberCycle_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {n : ℕ} {zeroDatum infinityDatum : FiniteSubschemeDatum f n}
    (P : FiniteSubschemeDatumPencil f n zeroDatum infinityDatum) :
    (FiniteSubschemeDatumPencil.toRationalCycleFamily f P).fiberCycle false =
      finiteSubschemeDatumCycle f zeroDatum := by
  exact rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_datumCycle
    f n P.datum false zeroDatum P.zeroIso P.zero_over

/-- The infinity endpoint of a finite-subscheme pencil carries exactly the
canonical cycle of its specified infinity datum. -/
theorem FiniteSubschemeDatumPencil.fiberCycle_infinity
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {n : ℕ} {zeroDatum infinityDatum : FiniteSubschemeDatum f n}
    (P : FiniteSubschemeDatumPencil f n zeroDatum infinityDatum) :
    (FiniteSubschemeDatumPencil.toRationalCycleFamily f P).fiberCycle true =
      finiteSubschemeDatumCycle f infinityDatum := by
  exact rationalCycleFamily_of_finiteSubschemeDatum_fiberCycle_eq_datumCycle
    f n P.datum true infinityDatum P.infinityIso P.infinity_over

/-- The endpoint data of an ideal-defined finite-flat pencil have the same
class in the quotient generated by finite-flat curve families. -/
theorem FiniteSubschemeDatumPencil.cycleClass_eq
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {n : ℕ} {zeroDatum infinityDatum : FiniteSubschemeDatum f n}
    (P : FiniteSubschemeDatumPencil f n zeroDatum infinityDatum) :
    PfaffianDescent.curveFamilyCycleClass f (finiteSubschemeDatumCycle f zeroDatum).toZeroCycle =
      PfaffianDescent.curveFamilyCycleClass f
        (finiteSubschemeDatumCycle f infinityDatum).toZeroCycle := by
  rw [← FiniteSubschemeDatumPencil.fiberCycle_zero f P,
    ← FiniteSubschemeDatumPencil.fiberCycle_infinity f P]
  exact PfaffianDescent.curveFamilyCycleClass_fibers f
    (FiniteSubschemeDatumPencil.toRationalCycleFamily f P)

/-- The finite-flat-family cycle class of a finite-subscheme datum depends
only on its isomorphism class over the ambient scheme.  Complete-intersection
families naturally supply these endpoint isomorphisms, whereas equality of
the two ideal presentations is generally unavailable. -/
theorem finiteSubschemeDatum_cycleClass_eq_of_iso
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {n : ℕ} (D E : FiniteSubschemeDatum f n)
    (e : D.val.subscheme ≅ E.val.subscheme)
    (he : e.hom ≫ E.val.subschemeι = D.val.subschemeι) :
    PfaffianDescent.curveFamilyCycleClass f
      (finiteSubschemeDatumCycle f D).toZeroCycle =
      PfaffianDescent.curveFamilyCycleClass f
        (finiteSubschemeDatumCycle f E).toZeroCycle := by
  rw [finiteSubschemeDatumCycle_eq_of_iso f D E e he]

end AllCharacteristics
