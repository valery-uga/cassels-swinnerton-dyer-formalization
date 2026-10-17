import PfaffianDescent.GrassmannianOverlapIsomorphism
import PfaffianDescent.GrassmannianTransitionCocycle
import PfaffianDescent.SchemeAffineFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {m n : ℕ}

/-- Evaluate the overlap minor under any ring map, without a chosen algebra structure. -/
lemma grassmannianOverlapPolynomial_map {A : Type u} [CommRing A]
    (φ : GrassmannianChartRing K m n →+* A) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    φ (grassmannianOverlapPolynomial K σ) =
      graphOverlapDeterminant (graphCoordinatePermutation A σ)
        (Matrix.toLin' (fun i j => φ (MvPolynomial.X (i, j)))) := by
  let U : Matrix (Fin n) (Fin m) (GrassmannianChartRing K m n) :=
    Matrix.of (fun i j => MvPolynomial.X (i, j))
  change φ (graphOverlapMatrix σ U).det = _
  rw [RingHom.map_det]
  change ((graphOverlapMatrix σ U).map φ).det = _
  rw [graphOverlapMatrix_map, graphOverlapMatrix_det]
  rfl

noncomputable def grassmannianChartToBase (m n : ℕ) :
    grassmannianChartScheme K m n ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom MvPolynomial.C)

/-- Matrix coordinates of a scheme-valued point of a Grassmannian chart. -/
noncomputable def grassmannianChartMatrix {X : Scheme.{u}}
    (f : X ⟶ grassmannianChartScheme K m n) : Matrix (Fin n) (Fin m) Γ(X, ⊤) :=
  fun i j => affineFunctionHom f (MvPolynomial.X (i, j))

lemma grassmannianChartMatrix_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ grassmannianChartScheme K m n) :
    grassmannianChartMatrix K (f ≫ g) = (grassmannianChartMatrix K g).map f.appTop.hom := by
  ext i j
  exact RingHom.congr_fun (affineFunctionHom_comp f g) (MvPolynomial.X (i, j))

lemma grassmannianChart_morphism_ext {X : Scheme.{u}}
    (f g : X ⟶ grassmannianChartScheme K m n)
    (hb : f ≫ grassmannianChartToBase K m n = g ≫ grassmannianChartToBase K m n)
    (hT : grassmannianChartMatrix K f = grassmannianChartMatrix K g) : f = g := by
  apply affineFunctionHom_injective
  apply MvPolynomial.ringHom_ext'
  · have h := congrArg affineFunctionHom hb
    exact (affineFunctionHom_comp_Spec f MvPolynomial.C).symm.trans
      (h.trans (affineFunctionHom_comp_Spec g MvPolynomial.C))
  · rintro ⟨i, j⟩
    exact congrFun (congrFun hT i) j

/-- Factoring through an actual principal-open overlap is equivalent to an invertible matrix block. -/
lemma grassmannianChart_factor_iff {X : Scheme.{u}}
    (f : X ⟶ grassmannianChartScheme K m n) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (∃ g : X ⟶ grassmannianOverlapScheme K σ, g ≫ grassmannianOverlapι K σ = f) ↔
      Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ)
        (Matrix.toLin' (grassmannianChartMatrix K f))) := by
  rw [show (∃ g : X ⟶ grassmannianOverlapScheme K σ, g ≫ grassmannianOverlapι K σ = f) ↔
      IsUnit (affineFunctionHom f (grassmannianOverlapPolynomial K σ)) from
        affineLocalization_factor_iff f (grassmannianOverlapPolynomial K σ)]
  rw [grassmannianOverlapPolynomial_map, graphOverlapDeterminant_isUnit_iff]
  rfl

/-- The factorization morphism used to enter a third chart on an intersection. -/
noncomputable def grassmannianChartLift {X : Scheme.{u}}
    (f : X ⟶ grassmannianChartScheme K m n) (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ)
      (Matrix.toLin' (grassmannianChartMatrix K f)))) : X ⟶ grassmannianOverlapScheme K σ :=
  affineLocalizationLift f (grassmannianOverlapPolynomial K σ)
    ((grassmannianOverlapPolynomial_map K (affineFunctionHom f) σ).symm ▸
      (graphOverlapDeterminant_isUnit_iff _ _).mpr h)

lemma grassmannianChartLift_fac {X : Scheme.{u}}
    (f : X ⟶ grassmannianChartScheme K m n) (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ)
      (Matrix.toLin' (grassmannianChartMatrix K f)))) :
    grassmannianChartLift K f σ h ≫ grassmannianOverlapι K σ = f :=
  affineLocalizationLift_fac f _ _

lemma grassmannianChartMatrix_overlap {X : Scheme.{u}}
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (g : X ⟶ grassmannianOverlapScheme K σ) :
    grassmannianChartMatrix K (g ≫ grassmannianOverlapι K σ) =
      (grassmannianOverlapUniversalMatrix K σ).map (affineFunctionHom g) := by
  ext i j
  exact RingHom.congr_fun (affineFunctionHom_comp_Spec g (algebraMap _ _)) (MvPolynomial.X (i, j))

lemma grassmannianChartMatrix_other {X : Scheme.{u}}
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (g : X ⟶ grassmannianOverlapScheme K σ) :
    grassmannianChartMatrix K (g ≫ grassmannianOverlapOtherι K σ) =
      (grassmannianOverlapTransitionMatrix K σ).map (affineFunctionHom g) := by
  rw [grassmannianOverlapOtherι_eq]
  ext i j
  have he := RingHom.congr_fun (affineFunctionHom_comp_Spec g
    (MvPolynomial.aeval (R := K) (fun ij : Fin n × Fin m =>
      grassmannianOverlapTransitionMatrix K σ ij.1 ij.2)).toRingHom) (MvPolynomial.X (i, j))
  exact he.trans (congrArg (affineFunctionHom g) (MvPolynomial.aeval_X _ (i, j)))

/-- The scheme transition has exactly the matrix transition formula on every test scheme. -/
lemma grassmannianChartMatrix_transition {X : Scheme.{u}}
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (g : X ⟶ grassmannianOverlapScheme K σ)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ)
      (Matrix.toLin' (grassmannianChartMatrix K (g ≫ grassmannianOverlapι K σ))))) :
    grassmannianChartMatrix K (g ≫ grassmannianOverlapOtherι K σ) =
      graphTransitionMatrix σ (grassmannianChartMatrix K (g ≫ grassmannianOverlapι K σ)) h := by
  rw [grassmannianChartMatrix_other]
  exact graphTransition_matrix_map_of_eq (affineFunctionHom g) σ
    (grassmannianOverlapUniversalMatrix K σ) _ (grassmannianChartMatrix_overlap K σ g).symm
    (grassmannianOverlapUniversal_bijective K σ) h

end
end PfaffianDescent
