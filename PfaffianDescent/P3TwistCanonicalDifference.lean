import PfaffianDescent.P3TwistTensorEquivalence
import PfaffianDescent.ProjectiveMixedTwistPairing

/-! # Concrete positive/negative degree subtraction on projective three-space

The three actual pairings O(m) tensor O(-4) -> O(-(4-m)), m=1,2,3,
are isomorphisms. The proof uses their actual homogeneous multiplication
squares and the standard coordinate cover.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

private theorem pairing_1_four_raw_square (s : PS 3) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous PS s 1).val
      (𝟙 (modulePresheaf PS 4)) ≫ positiveNegativePairingPresheaf PS 4 =
    positiveNegativeDifferencePairingPresheaf PS 1 4 (of_decide_eq_true rfl) ≫
      (mulHomogeneous PS s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1)
      (s : MvPolynomial (Fin 4) K) * p.1 x) * q.1 x =
    algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1)
      (s : MvPolynomial (Fin 4) K) * (p.1 x * q.1 x)
  ring

private theorem pairing_1_four_square (s : PS 3) :
    schemeModuleTensorMap (positiveMulHomogeneous PS s 1)
      (𝟙 (sheafOfModules PS 4)) ≫ positiveNegativePairing PS 4 =
    positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl) ≫ mulHomogeneous PS s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj PS).ringCatSheaf.obj)
  have hpair : adj.homEquiv _ _ (positiveNegativePairing PS 4) =
      positiveNegativePairingPresheaf PS 4 := (adj.homEquiv _ _).apply_symm_apply _
  have hdiff : adj.homEquiv _ _
      (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl)) =
      positiveNegativeDifferencePairingPresheaf PS 1 4 (of_decide_eq_true rfl) :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact pairing_1_four_raw_square K s

theorem p3CoordinatePositiveNegativeDifferencePairing_1_four_isIso (j : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl))) := by
  let U := p3StandardOpen (K := K) j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) 3
  have hspan : (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range (fun f : PS 1 => (f : MvPolynomial (Fin 4) K))) :=
    (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨p3Coordinate K i, rfl⟩))
  have hU : homogeneousBasicOpen PS (s : MvPolynomial (Fin 4) K) = U := by
    exact ProjectiveSpectrum.basicOpen_pow PS (MvPolynomial.X j) 3 (of_decide_eq_true rfl)
  letI : IsIso (F.map (positiveMulHomogeneous PS s 1)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen PS s 1 hspan
  letI : IsIso (F.map (mulHomogeneous PS s 0)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_mulHomogeneous_isIso_on_basicOpen PS s 0 hspan
  letI : IsIso (F.map (positiveNegativePairing PS 4)) :=
    p3CoordinatePositiveNegativePairing_isIso K j 4
  letI : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous PS s 1) (𝟙 (sheafOfModules PS 4)))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s 1) (𝟙 (sheafOfModules PS 4))
  have h := congrArg F.map (pairing_1_four_square K s)
  rw [F.map_comp, F.map_comp] at h
  haveI : IsIso (F.map (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl)) ≫
      F.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (F.map (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl)))
    (F.map (mulHomogeneous PS s 0))

theorem p3PositiveNegativeDifferencePairing_1_four_isIso :
    IsIso (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl)) := by
  let U := p3StandardOpenLifted (K := K)
  let F : ∀ j : P3CoordinateIndex, (Proj PS).Modules ⥤
      SheafOfModules ((Proj PS).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj PS).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U
      (p3StandardOpenLifted_coversTop K)
  letI : ∀ j, IsIso ((F j).map
      (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl))) := fun j => by
    letI : IsIso ((Scheme.Modules.restrictFunctor
        (p3StandardOpen (K := K) j.down).ι).map
        (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl))) :=
      p3CoordinatePositiveNegativeDifferencePairing_1_four_isIso K j.down
    exact overFunctorMap_isIso_of_restrictMap_isIso
      (p3StandardOpen (K := K) j.down)
      (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl))
  exact hF.isIso (positiveNegativeDifferencePairing PS 1 4 (of_decide_eq_true rfl))

private theorem pairing_2_four_raw_square (s : PS 2) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous PS s 2).val
      (𝟙 (modulePresheaf PS 4)) ≫ positiveNegativePairingPresheaf PS 4 =
    positiveNegativeDifferencePairingPresheaf PS 2 4 (of_decide_eq_true rfl) ≫
      (mulHomogeneous PS s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1)
      (s : MvPolynomial (Fin 4) K) * p.1 x) * q.1 x =
    algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1)
      (s : MvPolynomial (Fin 4) K) * (p.1 x * q.1 x)
  ring

private theorem pairing_2_four_square (s : PS 2) :
    schemeModuleTensorMap (positiveMulHomogeneous PS s 2)
      (𝟙 (sheafOfModules PS 4)) ≫ positiveNegativePairing PS 4 =
    positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl) ≫ mulHomogeneous PS s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj PS).ringCatSheaf.obj)
  have hpair : adj.homEquiv _ _ (positiveNegativePairing PS 4) =
      positiveNegativePairingPresheaf PS 4 := (adj.homEquiv _ _).apply_symm_apply _
  have hdiff : adj.homEquiv _ _
      (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl)) =
      positiveNegativeDifferencePairingPresheaf PS 2 4 (of_decide_eq_true rfl) :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact pairing_2_four_raw_square K s

theorem p3CoordinatePositiveNegativeDifferencePairing_2_four_isIso (j : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl))) := by
  let U := p3StandardOpen (K := K) j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) 2
  have hspan : (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range (fun f : PS 1 => (f : MvPolynomial (Fin 4) K))) :=
    (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨p3Coordinate K i, rfl⟩))
  have hU : homogeneousBasicOpen PS (s : MvPolynomial (Fin 4) K) = U := by
    exact ProjectiveSpectrum.basicOpen_pow PS (MvPolynomial.X j) 2 (of_decide_eq_true rfl)
  letI : IsIso (F.map (positiveMulHomogeneous PS s 2)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen PS s 2 hspan
  letI : IsIso (F.map (mulHomogeneous PS s 0)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_mulHomogeneous_isIso_on_basicOpen PS s 0 hspan
  letI : IsIso (F.map (positiveNegativePairing PS 4)) :=
    p3CoordinatePositiveNegativePairing_isIso K j 4
  letI : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous PS s 2) (𝟙 (sheafOfModules PS 4)))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s 2) (𝟙 (sheafOfModules PS 4))
  have h := congrArg F.map (pairing_2_four_square K s)
  rw [F.map_comp, F.map_comp] at h
  haveI : IsIso (F.map (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl)) ≫
      F.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (F.map (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl)))
    (F.map (mulHomogeneous PS s 0))

theorem p3PositiveNegativeDifferencePairing_2_four_isIso :
    IsIso (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl)) := by
  let U := p3StandardOpenLifted (K := K)
  let F : ∀ j : P3CoordinateIndex, (Proj PS).Modules ⥤
      SheafOfModules ((Proj PS).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj PS).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U
      (p3StandardOpenLifted_coversTop K)
  letI : ∀ j, IsIso ((F j).map
      (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl))) := fun j => by
    letI : IsIso ((Scheme.Modules.restrictFunctor
        (p3StandardOpen (K := K) j.down).ι).map
        (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl))) :=
      p3CoordinatePositiveNegativeDifferencePairing_2_four_isIso K j.down
    exact overFunctorMap_isIso_of_restrictMap_isIso
      (p3StandardOpen (K := K) j.down)
      (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl))
  exact hF.isIso (positiveNegativeDifferencePairing PS 2 4 (of_decide_eq_true rfl))

private theorem pairing_3_four_raw_square (s : PS 1) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous PS s 3).val
      (𝟙 (modulePresheaf PS 4)) ≫ positiveNegativePairingPresheaf PS 4 =
    positiveNegativeDifferencePairingPresheaf PS 3 4 (of_decide_eq_true rfl) ≫
      (mulHomogeneous PS s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1)
      (s : MvPolynomial (Fin 4) K) * p.1 x) * q.1 x =
    algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1)
      (s : MvPolynomial (Fin 4) K) * (p.1 x * q.1 x)
  ring

private theorem pairing_3_four_square (s : PS 1) :
    schemeModuleTensorMap (positiveMulHomogeneous PS s 3)
      (𝟙 (sheafOfModules PS 4)) ≫ positiveNegativePairing PS 4 =
    positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl) ≫ mulHomogeneous PS s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj PS).ringCatSheaf.obj)
  have hpair : adj.homEquiv _ _ (positiveNegativePairing PS 4) =
      positiveNegativePairingPresheaf PS 4 := (adj.homEquiv _ _).apply_symm_apply _
  have hdiff : adj.homEquiv _ _
      (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl)) =
      positiveNegativeDifferencePairingPresheaf PS 3 4 (of_decide_eq_true rfl) :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact pairing_3_four_raw_square K s

theorem p3CoordinatePositiveNegativeDifferencePairing_3_four_isIso (j : Fin 4) :
    IsIso ((Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl))) := by
  let U := p3StandardOpen (K := K) j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) 1
  have hspan : (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range (fun f : PS 1 => (f : MvPolynomial (Fin 4) K))) :=
    (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨p3Coordinate K i, rfl⟩))
  have hU : homogeneousBasicOpen PS (s : MvPolynomial (Fin 4) K) = U := by
    exact ProjectiveSpectrum.basicOpen_pow PS (MvPolynomial.X j) 1 (of_decide_eq_true rfl)
  letI : IsIso (F.map (positiveMulHomogeneous PS s 3)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen PS s 3 hspan
  letI : IsIso (F.map (mulHomogeneous PS s 0)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_mulHomogeneous_isIso_on_basicOpen PS s 0 hspan
  letI : IsIso (F.map (positiveNegativePairing PS 4)) :=
    p3CoordinatePositiveNegativePairing_isIso K j 4
  letI : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous PS s 3) (𝟙 (sheafOfModules PS 4)))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s 3) (𝟙 (sheafOfModules PS 4))
  have h := congrArg F.map (pairing_3_four_square K s)
  rw [F.map_comp, F.map_comp] at h
  haveI : IsIso (F.map (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl)) ≫
      F.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (F.map (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl)))
    (F.map (mulHomogeneous PS s 0))

theorem p3PositiveNegativeDifferencePairing_3_four_isIso :
    IsIso (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl)) := by
  let U := p3StandardOpenLifted (K := K)
  let F : ∀ j : P3CoordinateIndex, (Proj PS).Modules ⥤
      SheafOfModules ((Proj PS).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj PS).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U
      (p3StandardOpenLifted_coversTop K)
  letI : ∀ j, IsIso ((F j).map
      (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl))) := fun j => by
    letI : IsIso ((Scheme.Modules.restrictFunctor
        (p3StandardOpen (K := K) j.down).ι).map
        (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl))) :=
      p3CoordinatePositiveNegativeDifferencePairing_3_four_isIso K j.down
    exact overFunctorMap_isIso_of_restrictMap_isIso
      (p3StandardOpen (K := K) j.down)
      (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl))
  exact hF.isIso (positiveNegativeDifferencePairing PS 3 4 (of_decide_eq_true rfl))

end PfaffianDescent.ProjectiveNegativeTwist
