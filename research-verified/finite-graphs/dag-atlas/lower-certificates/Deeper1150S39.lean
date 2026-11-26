import AtlasCut

namespace CutWords1150
open AtlasLower AtlasMemo
set_option maxRecDepth 14000
set_option maxHeartbeats 9500000

def s39 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]

private def z39c0 : State := [0x810204081020400000000000000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e0 : optimized 6 0 z39c0 = false := by decide +kernel

private def z39c1 : State := [0x810204081020401fc00001fc000, 0x142850a142850a00000000000000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e1 : optimized 6 0 z39c1 = false := by decide +kernel

private def z39c2 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x8102040810204000000000000000, 0xa142850a1428500000000000007f]
private theorem e2 : optimized 6 0 z39c2 = false := by decide +kernel

private def z39c3 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xbf7efdfbf7efdf0000000000007f]
private theorem e3 : optimized 6 0 z39c3 = false := by decide +kernel

private def z39c4 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x89122448912244fffffff01fc000, 0xa142850a1428500000000000007f]
private theorem e4 : optimized 6 0 z39c4 = false := by decide +kernel

private def z39c5 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x952a54a952a54affffffffe03f80, 0xa142850a1428500000000000007f]
private theorem e5 : optimized 6 0 z39c5 = false := by decide +kernel

private def z39c6 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e6 : optimized 6 0 z39c6 = false := by decide +kernel

private def z39c7 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xe1c3870e1c3870ffffffffffff80]
private theorem e7 : optimized 6 0 z39c7 = false := by decide +kernel

private def z39c8 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x68d1a3468d1a3401fc000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e8 : optimized 6 0 z39c8 = false := by decide +kernel

private def z39c9 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x74e9d3a74e9d3afe03f80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e9 : optimized 6 0 z39c9 = false := by decide +kernel

private def z39c10 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e10 : optimized 6 0 z39c10 = false := by decide +kernel

private def z39c11 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x60c183060c18300000000fffff80, 0xa142850a1428500000000000007f, 0xc3870e1c3870e1fffffff0000000]
private theorem e11 : optimized 6 1 z39c11 = false := by decide +kernel

private def z39c12 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f, 0xbf7efdfbf7efdf0000000000007f]
private theorem e12 : optimized 6 0 z39c12 = false := by decide +kernel

private def z39c13 : State := [0x810204081020401fc00001fc000, 0x142850a142850afe03f80fe03f80, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xbf7efdfbf7efdf0000000000007f]
private theorem e13 : optimized 6 1 z39c13 = false := by decide +kernel

private def z39c14 : State := [0x810204081020401fc00001fc000, 0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e14 : optimized 6 0 z39c14 = false := by decide +kernel

private def z39c15 : State := [0x810204081020401fc00001fc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x56ad5ab56ad5abfe03ffffe03f80, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e15 : optimized 6 0 z39c15 = false := by decide +kernel

private def z39c16 : State := [0x810204081020401fc00001fc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x74e9d3a74e9d3afe03f80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e16 : optimized 6 0 z39c16 = false := by decide +kernel

private def z39c17 : State := [0x810204081020401fc00001fc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0x952a54a952a54affffffffe03f80, 0xa142850a1428500000000000007f]
private theorem e17 : optimized 6 0 z39c17 = false := by decide +kernel

private def z39c18 : State := [0x810204081020401fc00001fc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x952a54a952a54affffffffe03f80, 0xa142850a1428500000000000007f]
private theorem e18 : optimized 6 1 z39c18 = false := by decide +kernel

private def z39c19 : State := [0x810204081020401fc00001fc000, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x74e9d3a74e9d3afe03f80fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e19 : optimized 6 1 z39c19 = false := by decide +kernel

private def z39c20 : State := [0x142850a142850afe03f80fe03f80, 0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e20 : optimized 6 0 z39c20 = false := by decide +kernel

private def z39c21 : State := [0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x4a952a54a952a501fc07f01fc000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e21 : optimized 6 0 z39c21 = false := by decide +kernel

private def z39c22 : State := [0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x68d1a3468d1a3401fc000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e22 : optimized 6 0 z39c22 = false := by decide +kernel

private def z39c23 : State := [0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0x89122448912244fffffff01fc000, 0xa142850a1428500000000000007f]
private theorem e23 : optimized 6 0 z39c23 = false := by decide +kernel

private def z39c24 : State := [0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x89122448912244fffffff01fc000, 0xa142850a1428500000000000007f]
private theorem e24 : optimized 6 1 z39c24 = false := by decide +kernel

private def z39c25 : State := [0x142850a142850afe03f80fe03f80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x68d1a3468d1a3401fc000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e25 : optimized 6 1 z39c25 = false := by decide +kernel

private def z39c26 : State := [0x1c3870e1c3870efffff80fffff80, 0x1e3c78f1e3c78f0000000000007f, 0x42850a142850a1000007f0000000, 0x60c183060c18300000000fffff80, 0x81020408102040fffffff0000000, 0xa142850a1428500000000000007f]
private theorem e26 : optimized 6 1 z39c26 = false := by decide +kernel

private def next : Layer := #[z39c0,z39c1,z39c2,z39c3,z39c4,z39c5,z39c6,z39c7,z39c8,z39c9,z39c10,z39c11,z39c12,z39c13,z39c14,z39c15,z39c16,z39c17,z39c18,z39c19,z39c20,z39c21,z39c22,z39c23,z39c24,z39c25,z39c26]
private theorem afterStep : AtlasCut.Anchors 6 next := by
  intro s mem nd
  simp only [next, Array.mem_def, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact AtlasCut.leaf e0 nd
  · exact AtlasCut.leaf e1 nd
  · exact AtlasCut.leaf e2 nd
  · exact AtlasCut.leaf e3 nd
  · exact AtlasCut.leaf e4 nd
  · exact AtlasCut.leaf e5 nd
  · exact AtlasCut.leaf e6 nd
  · exact AtlasCut.leaf e7 nd
  · exact AtlasCut.leaf e8 nd
  · exact AtlasCut.leaf e9 nd
  · exact AtlasCut.leaf e10 nd
  · exact AtlasCut.leaf e11 nd
  · exact AtlasCut.leaf e12 nd
  · exact AtlasCut.leaf e13 nd
  · exact AtlasCut.leaf e14 nd
  · exact AtlasCut.leaf e15 nd
  · exact AtlasCut.leaf e16 nd
  · exact AtlasCut.leaf e17 nd
  · exact AtlasCut.leaf e18 nd
  · exact AtlasCut.leaf e19 nd
  · exact AtlasCut.leaf e20 nd
  · exact AtlasCut.leaf e21 nd
  · exact AtlasCut.leaf e22 nd
  · exact AtlasCut.leaf e23 nd
  · exact AtlasCut.leaf e24 nd
  · exact AtlasCut.leaf e25 nd
  · exact AtlasCut.leaf e26 nd
private theorem completeStep : (#[s39] : Layer).all (stateOK next 7) = true := by decide +kernel
theorem node39 : s39.Nodup → ¬ live basicOps goal 7 s39.toFinset :=
  (AtlasCut.step afterStep completeStep) s39 (by simp)

end CutWords1150
