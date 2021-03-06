#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

typedef union {
    int32 i[2];
    double d;
} dbl;

typedef union {
    int32 i;
    float f;
} flt;

value gethi(value v) {
    dbl d;
    d.d = Double_val(v);
    return copy_int32(d.i[0]);
}

value getlo(value v) {
    dbl d;
    d.d = Double_val(v);
    return copy_int32(d.i[1]);
}

value getsgl(value v) {
    flt f;
    f.f = Double_val(v);
    return copy_int32(f.i);
}

value getflt(value v) {
    flt f;
    f.i = Int32_val(v);
    return copy_double(f.f);
}
