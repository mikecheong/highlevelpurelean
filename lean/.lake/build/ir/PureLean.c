// Lean compiler output
// Module: PureLean
// Imports: public import Init public meta import Init public import PureLean.HardBenchmarks public import PureLean.HoldoutBenchmarks public import PureLean.Algebra public import PureLean.OrderGalois public import PureLean.RelationsSets public import PureLean.LogicFunctions public import PureLean.InductiveCompilers public import PureLean.NumberTheory
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_purelean_PureLean_HardBenchmarks(uint8_t builtin);
lean_object* initialize_purelean_PureLean_HoldoutBenchmarks(uint8_t builtin);
lean_object* initialize_purelean_PureLean_Algebra(uint8_t builtin);
lean_object* initialize_purelean_PureLean_OrderGalois(uint8_t builtin);
lean_object* initialize_purelean_PureLean_RelationsSets(uint8_t builtin);
lean_object* initialize_purelean_PureLean_LogicFunctions(uint8_t builtin);
lean_object* initialize_purelean_PureLean_InductiveCompilers(uint8_t builtin);
lean_object* initialize_purelean_PureLean_NumberTheory(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_purelean_PureLean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_HardBenchmarks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_HoldoutBenchmarks(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_Algebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_OrderGalois(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_RelationsSets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_LogicFunctions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_InductiveCompilers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_purelean_PureLean_NumberTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
