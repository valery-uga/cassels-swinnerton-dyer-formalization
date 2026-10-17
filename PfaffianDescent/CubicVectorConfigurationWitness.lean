import PfaffianDescent.VoisinEightVectorConfigurationPoint
import PfaffianDescent.CubicElevenPointSurfaceJetWitness

/-!
Actual ordered and unordered configuration points associated to finitely
many nonzero projectively distinct cubic-surface vectors. The split finite
étale datum is the literal fibre of the configuration family. This realizes
the native eleven-point surface-jet witness in the configuration scheme.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicVector_exists_orderedConfiguration
    {K : Type u} [Field K] [Infinite K] (n : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : Fin n → Fin 4 → K)
    (hzero : ∀ i, p.eval (y i) = 0) (hnonzero : ∀ i, y i ≠ 0)
    (hprojective : ∀ i j, i ≠ j → ∀ c : K, c • y i ≠ y j) :
    ∃ (c : Fin 4 → K) (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0),
      ∃ (q : Fin n → (Spec (.of K) ⟶ hypersurface p hp))
        (A : Spec (.of K) ⟶
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left),
        (∀ i, q i = projectiveVectorSchemePointInLinearChart
          (equationIdeal p hp) c (y i)
          (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)) ∧
        Function.Injective q ∧
        A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom =
          Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
        (∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left = q i) := by
  obtain ⟨c, hc⟩ := exists_common_linear_chart_for_nonzero_vectors y hnonzero
  let q : Fin n → (Spec (.of K) ⟶ hypersurface p hp) := fun i =>
    projectiveVectorSchemePointInLinearChart (equationIdeal p hp) c (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)
  have hbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    intro i
    exact projectiveVectorSchemePointInLinearChart_toBase
      (equationIdeal p hp) c (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)
  have hqinj : Function.Injective q := by
    intro i j hij
    by_contra hne
    exact (projectiveVectorSchemePointInLinearChart_ne_of_directions
      (equationIdeal p hp) c
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i))
      (cubicVector_zero_equationIdeal p hp (y j) (hzero j))
      (hc i) (hc j) (hprojective i j hne)) hij
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp)
  obtain ⟨A, hA, hcoords⟩ := exists_orderedConfigurationFieldPoint
    (hypersurfaceToBase p hp) n (Spec.map (CommRingCat.ofHom (RingHom.id K)))
    q hbase (fun i j hij => hqinj.ne hij)
  exact ⟨c, hc, q, A, (fun _ => rfl), hqinj, hA, hcoords⟩

theorem cubicVector_exists_orderedFiniteDatum
    {K : Type u} [Field K] [Infinite K] (n : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (y : Fin n → Fin 4 → K)
    (hzero : ∀ i, p.eval (y i) = 0) (hnonzero : ∀ i, y i ≠ 0)
    (hprojective : ∀ i j, i ≠ j → ∀ c : K, c • y i ≠ y j) :
    ∃ (c : Fin 4 → K) (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
      (q : Fin n → (Spec (.of K) ⟶ hypersurface p hp))
      (A : Spec (.of K) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
      (B : Spec (.of K) ⟶ cubicConfigurationBase p hp n)
      (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n),
      (∀ i, q i = projectiveVectorSchemePointInLinearChart
        (equationIdeal p hp) c (y i)
        (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)) ∧
      Function.Injective q ∧
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      A ≫ configurationQuotientMap (equationIdeal p hp) n = B ∧
      B ≫ cubicConfigurationToBase p hp n = Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      (∃ hB : B ≫ cubicConfigurationToBase p hp n = 𝟙 _,
        D = projectiveConfigurationFiniteSubschemeAt
          (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) n B hB) ∧
      Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      (∃ E : (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) ≅ D.val.subscheme,
        ∀ i, Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K))
          (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i) ∧
      (∀ i, (A ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left = q i) := by
  obtain ⟨c, hc, q, A, hq, hqinj, hA, hcoords⟩ :=
    cubicVector_exists_orderedConfiguration n p hp y hzero hnonzero hprojective
  let B : Spec (.of K) ⟶ cubicConfigurationBase p hp n :=
    A ≫ configurationQuotientMap (equationIdeal p hp) n
  have hBbase : B ≫ cubicConfigurationToBase p hp n =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    let I := equationIdeal p hp
    have hrel := configurationQuotientMap_toBase I n
    calc
      B ≫ cubicConfigurationToBase p hp n =
          A ≫ (configurationQuotientMap I n ≫ configurationQuotientToBase I n) :=
        Category.assoc _ _ _
      _ = A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom :=
        congrArg (fun f => A ≫ f) hrel
      _ = _ := hA
  have hBid : B ≫ cubicConfigurationToBase p hp n = 𝟙 _ := by simpa using hBbase
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp)
  have hsep' : IsSeparated (hypersurfaceToBase p hp) := inferInstance
  let D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n :=
    projectiveConfigurationFiniteSubschemeAt
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) n B hBid
  have hDet : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    @projectiveConfigurationFiniteSubschemeAt_toBase_etale
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' n B hBid
  let E : (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of K)) ≅ D.val.subscheme :=
    @projectiveConfigurationFiniteSubschemeAtIsoConstantCover
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' n A hBid
  have hSplit : ∀ i, Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of K))
      (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i := by
    intro i
    have hi := @projectiveConfigurationFiniteSubschemeAtIsoConstantCover_component_toProjective
      _ _ _ _ _ (grading (equationIdeal p hp)) _ _ _
      (hypersurfaceToBase p hp) hsep' n A hBid i
    exact hi.trans (hcoords i)
  exact ⟨c, hc, q, A, B, D, hq, hqinj, hA, rfl, hBbase,
    ⟨hBid, rfl⟩, hDet, ⟨E, hSplit⟩, hcoords⟩

/-- The full native surface-jet witness is realized by an actual ordered11
configuration and its literal split finite étale datum of length eleven. -/
theorem exists_cubicSurfaceElevenPoint_surface_jet_configuration_witness
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (x : Fin 11 → Fin 4 → K) (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet K)
      (hpx : ∀ i, aeval (x i) p = 0) (hpJ : ∀ i, aeval (J i) p = 0)
      (c : Fin 4 → K) (hc : ∀ i, (homogeneousLinearForm c).eval (x i) ≠ 0)
      (q : Fin 11 → (Spec (.of K) ⟶ hypersurface p hp))
      (A : Spec (.of K) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (B : Spec (.of K) ⟶ cubicConfigurationBase p hp 11)
      (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11),
      (∀ i, q i = projectiveVectorSchemePointInLinearChart
        (equationIdeal p hp) c (x i)
        (cubicVector_zero_equationIdeal p hp (x i) (hpx i)) (hc i)) ∧
      Function.Injective q ∧
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).hom =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      A ≫ configurationQuotientMap (equationIdeal p hp) 11 = B ∧
      B ≫ cubicConfigurationToBase p hp 11 = Spec.map (CommRingCat.ofHom (RingHom.id K)) ∧
      (∃ hB : B ≫ cubicConfigurationToBase p hp 11 = 𝟙 _,
        D = projectiveConfigurationFiniteSubschemeAt
          (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 11 B hB) ∧
      Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      (∃ E : (∐ fun _ : ULift.{u} (Fin 11) ↦ Spec (.of K)) ≅ D.val.subscheme,
        ∀ i, Sigma.ι (fun _ : ULift.{u} (Fin 11) ↦ Spec (.of K))
          (ULift.up i) ≫ E.hom ≫ D.val.subschemeι = q i) ∧
      (∀ i, (A ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 11)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 11 i).left = q i) ∧
      (∀ i j, (J i j).fst = x (i.castAdd 8) j) ∧
      Function.Surjective (cubicSurfaceElevenPointFullJetRestriction p hp x hpx J hpJ) ∧
      finrank K (LinearMap.ker (cubicSurfaceElevenPointValueRestriction p hp x hpx)) = 8 ∧
      Function.Surjective
        (cubicSurfaceElevenPointIdealFirstDerivativeRestriction p hp x hpx J hpJ) := by
  obtain ⟨x, J, hpx, hpJ, hx, hdir, hresidue, hfull, _, hdim, hderivative⟩ :=
    exists_cubicSurfaceElevenPoint_surface_fullJet_witness p hp hp0
  obtain ⟨c, hc, q, A, B, D, hq, hqinj, hA, hAB, hB, hD, hDet, hSplit, hcoords⟩ :=
    cubicVector_exists_orderedFiniteDatum 11 p hp x hpx hx hdir
  exact ⟨x, J, hpx, hpJ, c, hc, q, A, B, D, hq, hqinj, hA, hAB, hB,
    hD, hDet, hSplit, hcoords, hresidue, hfull, hdim, hderivative⟩

end PfaffianDescent
