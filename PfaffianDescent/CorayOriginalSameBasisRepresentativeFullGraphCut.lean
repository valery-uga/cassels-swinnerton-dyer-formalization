import PfaffianDescent.CorayOriginalSameGraphFullCutFiniteChartGuards
import PfaffianDescent.CorayOriginalNonzeroThroughPointSectionRepresentative
import PfaffianDescent.CorayAiNativeBasisDenominator

/-! SOURCE ONLY. Construct q0 from the SAME original basis coordinate b(a),
then choose the actual original-K graph matrix and literal full degree-three
cut/field/A, avoiding its SAME basis denominator and actual principal H.
No q0, point A, rank, cut maps, field or avoidance outcomes are inputs. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem actualChartMap_basisRepresentative_value_eq_sameDenominator001
    {K L M : Type u} [Field K] [CommRing L] [Algebra K L] [CommRing M]
    [Algebra K M]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (s : cubicThroughCoordinateSections p hp n y hpy) (hq : q.IsHomogeneous n)
    (hClass : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (x : Fin 4 → M) (hCoords : ∀ k, g (chartCoordinate (equationIdeal p hp) j k) = x k) :
    q.eval₂ (algebraMap K M) x = g (cubicThroughPointChartEvaluation p hp n y hpy j s) := by
  have hNormalized := cubicThroughPointSection_polynomial_normalized_eq_chartEvaluation001
    p hp n y hpy j s q hq hClass
  have hEval := MvPolynomial.hom_eval₂ q (chartBaseMap (equationIdeal p hp) j) g
    (chartCoordinate (equationIdeal p hp) j)
  rw [hBase] at hEval
  have hCoordsFun : (fun k => g (chartCoordinate (equationIdeal p hp) j k)) = x := funext hCoords
  rw [hCoordsFun, hNormalized] at hEval
  exact hEval.symm

/-- The SAME original basis b(a) supplies a fresh through-P q0 internally;
its scalar value equals the SAME retained native denominator. Honest H and
bad graph polynomial Q are the separate constructed geometry guards. -/
theorem originalSameBasis_noSection_exists_fixedGraph_fullDegreeThreeCut_basisRepresentative_nonzero001
    {K L : Type u} [Field K] [Infinite K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (hPivot : finSumFinEquiv (m := 2) (n := 2) (rho (Sum.inl (1 : Fin 2))) = j)
    :
    let R := ChartRing (equationIdeal p hp) j
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    ∀ H : R, H ≠ 0 →
    ∀ Q : GrassmannianChartRing K 2 2, Q ≠ 0 →
    ∃ q0 : MvPolynomial (Fin 4) K,
      q0.IsHomogeneous n ∧ q0.eval₂ (algebraMap K L) y = 0 ∧
      q0 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q0 = (b a).1.1 ∧
    ∃ T : Matrix (Fin 2) (Fin 2) K,
      MvPolynomial.eval (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) Q ≠ 0 ∧
      ∃ (c : Cubic K 4) (hc : c.toMvPolynomial = p),
      let aCol := originalGrassmannChartLineColumn001 rho T 0
      let bCol := originalGrassmannChartLineColumn001 rho T 1
      let iPivot := originalGrassmannChartLinePivot001 rho 0
      let F := cubicLinePolynomial c aCol bCol
      let B := AdjoinRoot F
      let x : Fin 4 → B :=
        AdjoinRoot.root F • (fun k => algebraMap K B (aCol k)) +
          (fun k => algebraMap K B (bCol k))
      let ell : MvPolynomial (Fin 4) K := X j - C (aCol j) * X iPivot
      let I := equationIdeal p hp
      ∃ hBFinite : Module.Finite K B,
        letI := hBFinite
        ∃ hField : IsField B,
          letI : Field B := hField.toField
          ∃ (hell : ell.IsHomogeneous 1)
            (hxell : ell.eval₂ (algebraMap K B) x = 1)
            (heI : ∀ f ∈ I.toIdeal, f.eval₂ (algebraMap K B) x = 0),
          let r : Spec (.of B) ⟶ hypersurface p hp :=
            linearNormalizedPoint I x ell hell hxell heI
          x j = 1 ∧
          (finiteProductCoordinateEquiv (R := B) 2 2).symm x ∈
            grassmannianChartSubmodule B rho (T.map (algebraMap K B)) ∧
          IsClosedImmersion r ∧
          r ≫ hypersurfaceToBase p hp =
            Spec.map (CommRingCat.ofHom (algebraMap K B)) ∧
          Module.finrank K B = 3 ∧
          ∃ g : R →ₐ[K] B,
            (∀ k, g (chartCoordinate I j k) = x k) ∧
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ chartι I j = r ∧
            g (cubicThroughPointChartEvaluation p hp n y hpy j (b a)) ≠ 0 ∧
            g H ≠ 0 ∧ q0.eval₂ (algebraMap K B) x ≠ 0 ∧
            Function.Surjective g ∧
            ∃ A : closedPoints (hypersurface p hp),
              A.1 = r (IsLocalRing.closedPoint B) ∧
              IsIso (r.residueFieldMap (IsLocalRing.closedPoint B)) ∧
              (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
  intro R
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  intro H hH Q hQ
  obtain ⟨q0, hq0, hqP, hqNot, hClass⟩ :=
    originalNonzeroThroughPointSection_exists_fresh_polynomial_representative001
      p hp n y hpy (b a) (b.ne_zero a)
  have hDen : cubicThroughPointChartEvaluation p hp n y hpy j (b a) ≠ 0 := by
    intro hzero
    apply b.ne_zero a
    apply cubicThroughPointChartEvaluation_injective p hp hp0 n y hpy j
    simpa only [map_zero] using hzero
  let v : Fin 2 → R := ![cubicThroughPointChartEvaluation p hp n y hpy j (b a), H]
  have hv : ∀ k, v k ≠ 0 := by
    intro k
    fin_cases k
    · exact hDen
    · exact hH
  let vLift : ULift.{u} (Fin 2) → R := fun i => v i.down
  have hvLift : ∀ i, vLift i ≠ 0 := fun i => hv i.down
  obtain ⟨T, hTQ, c, hc, hBFinite, hField, hell, hxell, heI,
      hxj, hxGraph, hClosed, hBase, hRank, g, hCoords, hFactor,
      hNonzero, hSurj, hA⟩ :=
    originalChartFunctions_noSection_exists_sameGraph_fullDegreeThreeCut_all_nonzero001
      (ι := ULift.{u} (Fin 2)) p hp hp0 hno j rho hPivot vLift hvLift Q hQ
  let aCol := originalGrassmannChartLineColumn001 rho T 0
  let bCol := originalGrassmannChartLineColumn001 rho T 1
  let F := cubicLinePolynomial c aCol bCol
  let B := AdjoinRoot F
  let x : Fin 4 → B :=
    AdjoinRoot.root F • (fun k => algebraMap K B (aCol k)) +
      (fun k => algebraMap K B (bCol k))
  letI : Module.Finite K B := hBFinite
  letI : Field B := hField.toField
  have hDenB : g (cubicThroughPointChartEvaluation p hp n y hpy j (b a)) ≠ 0 := hNonzero ⟨0⟩
  have hHB : g H ≠ 0 := hNonzero ⟨1⟩
  have hGBase : g.toRingHom.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K B :=
    RingHom.ext g.commutes
  have hValue := actualChartMap_basisRepresentative_value_eq_sameDenominator001
    p q0 hp n y hpy j (b a) hq0 hClass g.toRingHom hGBase x hCoords
  have hQ0B : q0.eval₂ (algebraMap K B) x ≠ 0 := by
    rw [hValue]
    exact hDenB
  exact ⟨q0, hq0, hqP, hqNot, hClass, T, hTQ, c, hc, hBFinite, hField,
    hell, hxell, heI, hxj, hxGraph, hClosed, hBase, hRank,
    g, hCoords, hFactor, hDenB, hHB, hQ0B, hSurj, hA⟩

end PfaffianDescent.Coray
