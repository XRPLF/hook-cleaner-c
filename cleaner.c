#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>

#define VERSION "1.1"
#define DEBUG 1
#define DEBUG_VERBOSE 0

#define MAX_TYPES 256
#define MAX_FUNCS 256   /* this includes imports! */

uint64_t leb(
    uint8_t** buf,
    uint8_t* bufend,
    int is_signed)
{
    uint64_t val = 0, shift = 0, i = 0;
    while (*buf + i < bufend)
    {
        uint64_t b = (uint64_t)((*buf)[i]);
        uint64_t last = val;
        val += (b & 0x7FU) << shift;
        if (val < last)
        {
            fprintf(stderr, "LEB128 overflow in input wasm at offset %ld.\n",
                    i);
            exit(100);
        }
        ++i;
        if (b & 0x80U)
        {
            shift += 7;
            continue;
        }
        *buf += i;

        if (is_signed && shift < 64 && (b & 0x40U))
            val |= (~0 << shift);

        return val;
    }
    return 0;
}

void leb_out(
    uint64_t i,
    uint8_t** o)
{
    do
    {
        uint8_t b = i & 0x7FU;
        i >>= 7U;
        if (i != 0)
            b |= 0x80;

        **o = b;
        (*o)++;
    } while (i != 0);
}


void leb_out_pad(
    uint64_t i,
    uint8_t** o,
    int padto)
{
    fprintf(stderr, "Leb_out_pad(i=%ld, pad=%d): [", i, padto);
    padto--;
    do
    {
        uint8_t b = i & 0x7FU;
        i >>= 7U;
        if (i != 0 || padto > 0)
            b |= 0x80;

        **o = b;
        (*o)++;
        fprintf(stderr, " 0x%02X", b);
        padto--;
    } while (i > 0 || padto >= 0);


    fprintf(stderr, " ]\n");
}

int cleaner (
    uint8_t*    w,      // web assembly input buffer
    uint8_t*    o,      // web assembly output buffer
    ssize_t*    len)    // length of input buffer when called, and len of output buffer when returned
{
    // require at least `need` bytes
    #define REQUIRE(need)\
    {\
        if (DEBUG && DEBUG_VERBOSE)\
            fprintf(stderr, "Require %ld b\tfrom 0x%lX to 0x%lX\n",\
                ((uint64_t)(need)),\
                ((uint64_t)(w-wstart)),\
                ((uint64_t)(w+need-wstart)));\
        if (wlen - (w - wstart) < need)\
            return \
                fprintf(stderr,\
                    "Truncated web assembly input. SrcLine: %d. Illegally short at position %ld [0x%lx].\n"\
                    "wlen: %ld w-wstart: %ld need:%ld\n"\
                    "%08lX : %02X %02X %02X %02X\n",\
                    __LINE__,\
                    ((uint64_t)(w - wstart)),\
                    ((uint64_t)(w - wstart)),\
                    ((uint64_t)(wlen)),\
                    ((uint64_t)(w-wstart)),\
                    ((uint64_t)(need)),\
                    ((uint64_t)((w - wstart) - 4)),\
                     *(w-4), *(w-3), *(w-2), *(w-1));\
    }

    // advance `adv` bytes
    #define ADVANCE(adv)\
    {\
        if (DEBUG && DEBUG_VERBOSE)\
            fprintf(stderr, "Advance %ld b\tfrom 0x%lX to 0x%lX\n",\
                ((uint64_t)(adv)),\
                ((uint64_t)(w-wstart)),\
                ((uint64_t)(w+adv-wstart)));\
        w += adv;\
        REQUIRE(0);\
    }

    
    #define LEB()\
        (tmp2=w-wstart,tmp=leb(&w, wend, 0),\
        (DEBUG && DEBUG_VERBOSE &&\
        fprintf(stderr, "Leb read at 0x%lX: %ld\n", tmp2, tmp)),tmp)

    #define SIGNED_LEB()\
        (tmp2=w-wstart,tmp=leb(&w, wend, 1),\
        (DEBUG && DEBUG_VERBOSE &&\
        fprintf(stderr, "Signed Leb read at 0x%lX: %ld\n", tmp2, tmp)),tmp)

    uint8_t*    wstart = w;  // remember start of buffer
    ssize_t     wlen = *len;
    uint8_t*    wend = w + wlen;
    uint64_t    tmp, tmp2;

    // read magic number
    REQUIRE(4);
    //00 61 73 6D
    if (w[0] != 0x00U || w[1] != 0x61U || w[2] != 0x73U || w[3] != 0x6DU)
        return fprintf(stderr, "Magic number missing or invalid %02X=%d %02X=%d %02X=%d %02X=%d\n",
                w[0], w[0] == 0x00U, w[1], w[1] == 0x61U, w[2], w[2] == 0x73U, w[3], w[3] == 0x6DU);
    ADVANCE(4);

    // read version
    REQUIRE(4)
    if (w[0] != 0x01U || w[1] || w[2] || w[3])
        return fprintf(stderr, "Only version 1.00 of WASM standard is supported\n");
    ADVANCE(4);

    // first section loop

    if (DEBUG)
        fprintf(stderr, "First pass start\n");

    int func_hook = -1;
    int func_cbak = -1;
    int mem_export = -1; // RH UPTO: find out what memory is exported and carry it over (do we need this??)
   
    int     out_import_count = -1;  // the number of imports there will be in the output file
    ssize_t out_import_size = 0;    // the size ofthe import section in the output
    
    ssize_t out_code_size = 0;

    int func_count = -1;
    int hook_cbak_type = -1;
    int func_type[MAX_FUNCS];    // each function we discover import/func has its type id recorded here
    struct {
        uint8_t set;
        uint8_t rc;
        uint8_t r[30];
        uint8_t pc;
        uint8_t p[31];
    } types[MAX_TYPES];

    for (int x = 0; x < MAX_TYPES; ++x)
    {
        func_type[x] = -1;
        types[x].set = 0;
    }

    int guard_func_idx = -1;
    uint8_t* next_section_start = 0;

    while (w < wend)
    {
        if (next_section_start && w != next_section_start)
        {
            return fprintf(stderr, "Internal sanity check failed. w = %ld, next_section_start = %ld\n",
                    w - wstart, next_section_start - wstart);
        }

        REQUIRE(1);
        uint8_t section_type = w[0];
        ADVANCE(1);

        uint64_t section_len = LEB();

        if (DEBUG)
            fprintf(stderr, "Section type: %d, Section len: %ld, Section offset: 0x%lX\n",
                section_type, section_len, w - wstart);

        REQUIRE(section_len);

        next_section_start = w + section_len;

        switch (section_type)
        {
            case 0x01U: // types
            {
                int type_count = LEB();
                for (int i = 0; i < type_count; ++i)
                {
                    REQUIRE(1);
                    if (w[0] != 0x60U)
                        return fprintf(stderr, "Illegal func type didn't start with 0x60U at %lX\n",
                                (w - wstart));
                    ADVANCE(1);

                    int param_count = LEB();

                    types[i].pc = param_count;

                    int is_P32 = 0;
                    for (int j = 0; j < param_count; ++j)
                    {
                        int param_type = LEB();
                        types[i].p[j] = param_type;

                        if (param_type == 0x7FU && param_count == 1)
                            is_P32 = 1;

                    }

                    int result_count = LEB();
                    types[i].set = 1;
                    types[i].rc = result_count;

                    if (result_count == 1)
                    for (int j = 0; j < result_count; ++j)
                    {
                        int result_type = LEB();
                        types[i].r[j] = result_type;

                        if (result_type == 0x7EU && result_count == 1 && is_P32)
                        {
                            if (DEBUG)
                                fprintf(stderr, "Hook/Cbak type: %d\n", i);
                            if (hook_cbak_type != -1)
                                return fprintf(stderr, "int64_t func(int32_t) appears in type section twice!\n");

                            hook_cbak_type = i;
                        }
                    }
                }
                continue;
            }

            case 0x02U: // imports
            {
                // just get an import count
                int count = LEB();
                if (DEBUG)
                    fprintf(stderr, "Import count: %d\n", count);

                int func_upto = 0;

                for (int i = 0; i < count; ++i)
                {
                    uint8_t* import_start = w;
                    // module name
                    int mod_length = LEB();
                    REQUIRE(mod_length);
                    if (mod_length != 3 || w[0] != 'e' || w[1] != 'n' || w[2] != 'v')
                        return fprintf(stderr, "Did not import only from module 'env'\n");
                    ADVANCE(mod_length);

                    // import name
                    int name_length = LEB();
                    REQUIRE(name_length);
                    if (name_length == 2 && w[0] == '_' && w[1] == 'g')
                    {
                        guard_func_idx = func_upto;
                        fprintf(stderr, "Guard function found at index: %d\n", guard_func_idx);
                    }
                    ADVANCE(name_length);


                    REQUIRE(1);
                    uint8_t import_type = w[0];
                    ADVANCE(1);

                    // only function imports
                    if (import_type != 0x00U)
                    {
                        if (guard_func_idx == i)
                            return fprintf(stderr, "Guard import _g was not imported as a function!\n");

                        if (import_type == 0x01U)
                        {
                            // table type
                            REQUIRE(1);
                            ADVANCE(1);
                            int dualLimit = (*w == 0x00U);
                            ADVANCE(1);
                            LEB();
                            if (dualLimit)
                                LEB();
                        }
                        else if (import_type == 0x02U)
                        {
                            // mem type
                            int dualLimit = (*w == 0x00U);
                            LEB();
                            if (dualLimit)
                                LEB();
                        }
                        else if (import_type == 0x03U)
                        {
                            REQUIRE(2);
                            ADVANCE(2);
                        }
                    }
                    else
                    {
                        uint64_t import_idx = LEB();
                        func_type[func_upto++] = import_idx;
                        out_import_size += (w - import_start);
                        if (DEBUG)
                            fprintf(stderr, "Import %d type %ld out_import_size = %ld\n",
                                func_upto, import_idx, out_import_size);
                    }
                }

                out_import_count = func_upto;

                if (out_import_count > 127*127)
                    return fprintf(stderr, "Unsupported number of imports: %d\n", out_import_count);

                out_import_size += (out_import_count <= 127 ? 1U : 2U);
                continue;
            }

            case 0x03U: // funcs
            {
                func_count = LEB();
                if (DEBUG)
                    fprintf(stderr, "Function count: %d\n", func_count);
                for (int i = 0; i < func_count; ++i)
                {
                    func_type[out_import_count + i] = LEB();
                    if (DEBUG)
                        fprintf(stderr, "Func %d is type %d\n",
                            out_import_count + i, func_type[out_import_count + i]);
                }
                continue;
            }

        

            case 0x07U: // exports
            {
                uint8_t* export_end = w + section_len; 
    
                uint64_t export_count = LEB();
            
                for (uint64_t i = 0; i < export_count; ++i)
                {
                    // we only care about two exports: hook and cbak
                    // since we have to parse name first we'll read it in passing
                    // and store info about it here
                    int status = 0; // 1 = hook() 2 = cbak(), 0 = irrelevant
                    
                    // read export name
                    uint64_t export_name_len = LEB();
                    REQUIRE(export_name_len);
                    if (export_name_len == 4)
                    {
                        if (w[0] == 'h' && w[1] == 'o' && w[2] == 'o' && w[3] == 'k')
                            status = 1;
                        else
                        if (w[0] == 'c' && w[1] == 'b' && w[2] == 'a' && w[3] == 'k')
                            status = 2;
                    }
                    ADVANCE(export_name_len);
                    
                    // export type
                    REQUIRE(1);
                    uint8_t export_type = w[0];
                    ADVANCE(1);

                    // export idx
                    uint64_t export_idx = LEB();

                    if (status == 1)
                        func_hook = export_idx;
                    else if (status == 2)
                        func_cbak = export_idx;

                    if (func_hook > -1 && func_cbak > -1)
                        break;
                }

                // hook() is required at minimum
                if (func_hook < 0)
                    return fprintf(stderr, "Could not find hook() export in wasm input\n");

                w = export_end;

                continue;
            }

            case 0x0AU:
            {
                uint64_t code_count = LEB();
                for (uint64_t i = 0; i < code_count; ++i)
                {
                    uint8_t* code_start = w;
                    uint64_t code_size = LEB();

                    ADVANCE(code_size);

                    if (i == (func_hook - out_import_count) || i == (func_cbak - out_import_count))
                        out_code_size += (w - code_start);
    
                }
                continue;
            }

            default:
            {
                ADVANCE(section_len);
                continue;
            }
        }

    }


    if (hook_cbak_type == -1)
        return fprintf(stderr, "Hook/cbak has the wrong function signature. Must be int64_t (*) (uint32_t).\n");

    fprintf(stderr, "hook idx: %d, cbak idx: %d\n", func_hook, func_cbak);


    if (guard_func_idx == -1)
        return fprintf(stderr, "Guard function _g was not imported / missing.\n");

    // reset to top
    w = wstart;

    // pass two: write out
    
    if (DEBUG)
        fprintf(stderr, "Second pass start\n");

    uint8_t* ostart = o;

    // magic number and version: 8 bytes
    for (int i = 0; i < 8; ++i)
        *o++ = *w++;

    int type_new[MAX_TYPES];
    memset(type_new, 0, sizeof(type_new));

    next_section_start = 0;

    while (w < wend)
    {

        if (next_section_start && w != next_section_start)
        {
            return fprintf(stderr, "Internal sanity check failed. w = %ld, next_section_start = %ld\n",
                    w - wstart, next_section_start - wstart);
        }

        REQUIRE(1);
        uint8_t section_type = w[0];
        ADVANCE(1);

        uint64_t section_len = LEB();

        if (DEBUG)
            fprintf(stderr, "Source section type: %d, Section len: %ld, Section offset: 0x%lX\n",
                section_type, section_len, w - wstart);

        REQUIRE(section_len);

        next_section_start = w + section_len;

        switch (section_type)
        {
            case 0x04U: // tables
            case 0x08U: // start
            case 0x09U: // elements
            case 0x00U: // custom section
            {
                // these sections are dropped
                ADVANCE(section_len);
                continue;
            }

            case 0x05U: // memory
            case 0x0BU: // data section
            case 0x0CU: // data count section
            {
                // copied as is
                *o++ = section_type;
                leb_out(section_len, &o);
                memcpy(o, w, section_len);
                o += section_len;
                ADVANCE(section_len);
                continue;
            }

            case 0x01U: // type section
            {
                ADVANCE(section_len);

                *o++ = 0x01U;   // write section type

                uint8_t used[MAX_TYPES];
                memset(used, 0, MAX_TYPES);

                // count types
                int type_count = 0;
                int imports_use_hook_cbak_type = 0;
                int section_size = 0;
                for (int i = 0; i < out_import_count; ++i)
                {
                    if (!used[func_type[i]])
                    {
                        type_count++;
                        used[func_type[i]] = 1;
                        section_size += 3U + types[func_type[i]].rc + types[func_type[i]].pc;
                        if (func_type[i] == hook_cbak_type && !imports_use_hook_cbak_type)
                        {
                            imports_use_hook_cbak_type = 1;
                            hook_cbak_type = type_count-1;
                            if (DEBUG)
                                fprintf(stderr, "Imports DO use hook_cbak_type = %d\n", hook_cbak_type);
                        }
                    }
                }
                
                if (!imports_use_hook_cbak_type)
                {
                    hook_cbak_type = type_count++;
                    section_size += 5U;
                    if (DEBUG)
                        fprintf(stderr, "Imports do not use hook_cbak_type = %d\n", hook_cbak_type);
                }
                
                if (type_count > 127*127)
                    return fprintf(stderr, "Too many types in wasm!\n");

                // account for the type vector size bytes
                section_size += (type_count > 127 ? 2U : 1U);

                if (DEBUG)
                    fprintf(stderr, "Writing type section, proposed size: %d\n", section_size);
                // write out section size
                leb_out(section_size, &o);


                uint8_t* out_start = o;

                // write type vector len
                leb_out(type_count, &o);

                // write out types
                memset(used, 0, MAX_TYPES);
                int upto = 0;
                for (int i = 0; i < out_import_count; ++i)
                {
                    int t = func_type[i];
                    if (!types[t].set)
                        return fprintf(stderr, "Tried to write unset type %d from func %d\n", func_type[i], i);
                    

                    if (used[t])
                        continue;
                    used[t] = 1;

                    *o++ = 0x60U;   // functype lead in byte
                    // write parameter count
                    leb_out(types[t].pc, &o);
                    // write each parameter type
                    for (int j = 0; j < types[t].pc; ++j)
                        leb_out(types[t].p[j], &o);
                
                    leb_out(types[t].rc, &o);
                    for (int j = 0; j < types[t].rc; ++j)
                        leb_out(types[t].r[j], &o);

                    type_new[t] = upto++;
                    // done for this record
                }

                // write out cbak/hook type if needed
                if (!imports_use_hook_cbak_type)
                {
                    *o++ = 0x60U;
                    *o++ = 0x01U;
                    *o++ = 0x7FU;
                    *o++ = 0x01U;
                    *o++ = 0x7EU;
                }

                if (DEBUG)
                    fprintf(stderr, "Actually written type section size: %ld\n", o - out_start);
                continue;
            }

            case 0x02U: // imports
            {
                *o++ = 0x02U;   

                if (DEBUG)
                {
                   fprintf(stderr, "Writing import section, proposed size, count: %ld, %d\n",
                           out_import_size, out_import_count);
                }

                leb_out(out_import_size, &o);
                uint8_t* import_start = o;
                leb_out(out_import_count, &o);

                int type_count = 0;
                
                int count = LEB();
                for (int i = 0; i < count; ++i)
                {
                    // module name
                    int mod_length = LEB();
                    REQUIRE(mod_length);
                    uint8_t* mod = w;
                    ADVANCE(mod_length);

                    // import name
                    int name_length = LEB();
                    REQUIRE(name_length);
                    uint8_t* name = w;
                    ADVANCE(name_length);

                    // only function imports
                    if (*w != 0x00U)
                    {
                        int it = *w;
                        ADVANCE(1);

                        if (it == 0x01U)
                        {
                            // table type
                            REQUIRE(1);
                            ADVANCE(1);
                            int dualLimit = (*w == 0x00U);
                            ADVANCE(1);
                            LEB();
                            if (dualLimit)
                                LEB();
                        }
                        else if (it == 0x02U)
                        {
                            // mem type
                            int dualLimit = (*w == 0x00U);
                            LEB();
                            if (dualLimit)
                                LEB();
                        }
                        else if (it == 0x03U)
                        {
                            REQUIRE(2);
                            ADVANCE(2);
                        }
                        continue;
                    }

                    ADVANCE(1);

                    // write mod 
                    leb_out(mod_length, &o);
                    memcpy(o, mod, mod_length);
                    o += mod_length;

                    // write name
                    leb_out(name_length, &o);
                    memcpy(o, name, name_length);
                    o += name_length;

                    // write import type (always 0)
                    *o++ = 0x00U;

                    if (DEBUG)
                        fprintf(stderr, "New import: %d old type: %d new type: %d\n", i, func_type[i], type_new[func_type[i]]);

                    // write new type idx
                    leb_out(type_new[func_type[i]], &o);

                    LEB(); // discard old type
                    // advance to next entry
                }

                if (DEBUG)
                    fprintf(stderr, "Actually written import size: %ld\n", o - import_start);

                continue;
            }

            case 0x03U: // functions
            {
                *o++ = 0x03U;
                

                ssize_t s = (func_cbak == -1 ? 0x01U : 0x02U);
                if (hook_cbak_type > 127U*127U)
                    return fprintf(stderr, "Illegally large hook_cbak type index\n");
                if (hook_cbak_type > 127U)
                    s <<= 1U;   // double size if > 127
                s++;            // one byte for the vector size
                if (DEBUG)
                    fprintf(stderr, "Writing function section, proposed size: %ld\n", s);

                leb_out(s, &o); // sections size
                uint8_t* function_start = o;
                *o++ = (func_cbak == -1 ? 0x01U : 0x02U);   // vector size
                leb_out(hook_cbak_type, &o);    // vector entries
                if (func_cbak != -1)
                {
                    leb_out(hook_cbak_type, &o);
                    if (DEBUG)
                        fprintf(stderr, "Writing cbak [idx=%d, type=%d]\n", func_cbak, hook_cbak_type);
                }
                ADVANCE(section_len);

                if (DEBUG)
                    fprintf(stderr, "Actually written function size: %ld\n", o - function_start);
                continue;
            }

            case 0x06U: // globals
            {
                // globals are copied byte for byte
                *o++ = 0x06U;
                leb_out(section_len, &o);
                memcpy(o, w, section_len);
                o += section_len;
                ADVANCE(section_len);
                continue;
            }

            case 0x07U: // exports
            {
                *o++ = 0x07U;
                
                // size
                // V M NNNN 0 1 [ M NNNN 0 2 ]
                *o++ = (func_cbak == -1 ? 0x08U : 0x0FU);

                // vec len
                *o++ = (func_cbak == -1 ? 0x01U : 0x02U);
    
                int cbak_first = (func_cbak < func_hook);

                if (cbak_first && func_cbak != -1)
                {
                    *o++ = 0x04U;
                    *o++ = 'c'; *o++ = 'b'; *o++ = 'a'; *o++ = 'k';
                    *o++ = 0x00U;
                    leb_out(out_import_count + 0, &o);
                    
                    *o++ = 0x04U;
                    *o++ = 'h'; *o++ = 'o'; *o++ = 'o'; *o++ = 'k';
                    *o++ = 0x00U;
                    leb_out(out_import_count + 1, &o);
                }
                else
                {
                    *o++ = 0x04U;
                    *o++ = 'h'; *o++ = 'o'; *o++ = 'o'; *o++ = 'k';
                    *o++ = 0x00U;
                    leb_out(out_import_count + 0, &o);

                    if (func_cbak != -1)
                    {
                        *o++ = 0x04U;
                        *o++ = 'c'; *o++ = 'b'; *o++ = 'a'; *o++ = 'k';
                        *o++ = 0x00U;
                        leb_out(out_import_count + 1, &o);
                    }
                }

                ADVANCE(section_len);
                continue;
            }

            case 0x0AU: // code section (aka function body)
            {
                *o++ = 0x0AU;

                if (DEBUG)
                    fprintf(stderr, "Output code size: %ld\n", out_code_size + 1);

    
                // RH NOTE:
                // In addition to moving a properly formed clean guard of the form { i32.const, i32.const, _g, drop }
                // we can also reinterpret a badly formed guard like { i32.con, i32.store, ..., i32.con, _g, drop }.
                // This becomes what's known as a guard rewrite. In this case additional instructions beyond the
                // original size of the hook will be inserted at the start of the relevant loop. This counter tracks
                // these, and the reserved space allows us to output the right LEB128 at the end.
                int total_guard_rewrite_bytes = 0;
                uint8_t* codesec_out_size_ptr = o;



                // we need to correct this at the end
                leb_out_pad(out_code_size + 1 /* allow for vec len */, &o, 3);

                *o++ = (func_cbak == -1 ? 0x01U : 0x02U); // vec len

                uint64_t count = LEB();
                for (uint64_t i = 0; i < count; ++i)
                {
                    uint8_t* code_start = w;
                    uint64_t code_size = LEB();
                    if (i == (func_hook - out_import_count) || i == (func_cbak - out_import_count))
                    {

                        //leb_out(code_size, &o);
                        int guard_rewrite_bytes = 0;
                        uint8_t* code_size_ptr = o;

                        // we need to correct this at the end
                        leb_out_pad(code_size, &o, 3);
                        
                        int pad_len = 3 - (w-code_start);
                        if (pad_len < 0)
                            return fprintf(stderr, 
                                    "Codesec %ld was too large! Size must fit in 3 leb128 bytes!\n", i);

                        total_guard_rewrite_bytes += pad_len;


                        //memcpy(o, code_start, w-code_start);

                        // parse locals
                        uint8_t* locals_start = w;
                        uint64_t locals_count = LEB();
                        fprintf(stderr, "Locals count: %ld\n", locals_count);
                        for (int i = 0; i < locals_count; ++i)
                        {
                            LEB();      // inner len
                            REQUIRE(1); // local type
                            ADVANCE(1);
                        }

                        memcpy(o, locals_start, w-locals_start);
                        o += (w-locals_start);

                        uint8_t* expr_start = w;
                        uint64_t expr_size = code_size - (w-locals_start);

                        fprintf(stderr, "Expr start: %ld [0x%lx]\n", expr_size, expr_size);

                        // parse code
                        uint8_t* last_loop = 0;         // where the start of the last loop instruction is in the input
                        uint8_t* last_loop_out = 0;     // where the start of the last loop instruction is in the output

                        int i32_found = 0;
                        uint8_t* call_guard_found = 0;
                        uint8_t* last_i32 = 0;
                        uint64_t last_i32_actual = 0;   // the actual leb value 
                        uint8_t* second_last_i32 = 0;
                        uint64_t second_last_i32_actual = 0; // the actual leb value
                        int between_const_and_guard = 0;

                        #define RESET_GUARD_FINDER()\
                        {\
                            i32_found = 0;\
                            call_guard_found = 0;\
                            last_i32 = 0;\
                            last_i32_actual = 0;\
                            second_last_i32 = 0;\
                            second_last_i32_actual = 0;\
                            between_const_and_guard = 0;\
                        }


                        while (w - expr_start < expr_size)
                        {
                            uint8_t* instr_start = w;

                            REQUIRE(1);
                            uint8_t ins = *w;
                            ADVANCE(1);

                            if (ins == 0x02U || ins == 0x03U || ins == 0x04U) // block, loop, if
                            {
                                REQUIRE(1);
                                uint8_t block_type = *w;
                                if ((block_type >= 0x7CU && block_type <= 0x7FU) ||
                                     block_type == 0x7BU || block_type == 0x70U || 
                                     block_type == 0x7BU || block_type == 0x40U)
                                {
                                    ADVANCE(1);
                                }
                                else
                                    SIGNED_LEB();


                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                
                                if (ins == 0x03U)                   // loop
                                {
                                    last_loop = w;
                                    last_loop_out = o;
                                }
                                
                                RESET_GUARD_FINDER();    
                                continue;
                            }
                            
                            if (ins == 0x1AU)                       // drop
                            {
                                REQUIRE(1);
                                *o++ = ins;
                                if (i32_found >= 2 && call_guard_found && last_loop)
                                {

                                    if (between_const_and_guard > 0)
                                    {

                                        if (second_last_i32_actual < last_i32_actual)
                                        {
                                            uint64_t swap = last_i32_actual;
                                            last_i32_actual = second_last_i32_actual;
                                            second_last_i32_actual = swap;
                                        }

                                        uint8_t guard_code[128];
                                        uint8_t* g = guard_code;
                                        *g++ = 0x41U;
                                        leb_out(second_last_i32_actual, &g);
                                        *g++ = 0x41U;
                                        leb_out(last_i32_actual, &g);
                                        *g++ = 0x10U;
                                        leb_out(guard_func_idx, &g);
                                        *g++ = 0x1AU;

                                        ssize_t guard_len = g - guard_code;
                                        ssize_t rest_len = w - last_loop;

                                        char guard_print[128]; guard_print[0] = '\0';
                                        snprintf(guard_print, 128, "_g(0x%08lx,%ld)", second_last_i32_actual,
                                                last_i32_actual);
                                        int guard_pad_len = 20 - strlen(guard_print);
                                        if (guard_pad_len < 0) guard_pad_len = 0;

                                        snprintf(guard_print, 128, "_g(0x%08lx,%.*s%ld)",
                                                second_last_i32_actual,
                                                guard_pad_len,
                                                "                     ",
                                                last_i32_actual);


                                        fprintf(stderr, "Found dirty guard %s\tat: %ld [0x%lx] - %ld [0x%lx],\t"
                                                "rewriting to %ld [0x%lx] - %ld [0x%lx]\n", 
                                                guard_print,
                                                second_last_i32 - wstart,
                                                second_last_i32 - wstart,
                                                w - wstart,
                                                w - wstart,
                                                last_loop - wstart,
                                                last_loop - wstart,
                                                last_loop - wstart + guard_len,
                                                last_loop - wstart + guard_len
                                            );

                                        // erase guard call with nops and an additional drop
                                        // to preserve the stack at this location during runtime
                                        int bytes_to_fill = w - call_guard_found - 2;
                                        *call_guard_found = 0x1AU;                      // drop
                                        while (bytes_to_fill-- > 0)
                                            *(++call_guard_found) = 0x01U;              // nop

                                        // first move the instructions down
                                        memcpy(last_loop_out + guard_len, last_loop, rest_len);

                                        // then copy the guard into position
                                        memcpy(last_loop_out, guard_code, guard_len);

                                        // prevent moving a second guard here if somehow there is one
                                        last_loop = 0;

                                        RESET_GUARD_FINDER();

                                        guard_rewrite_bytes += guard_len;
                                        total_guard_rewrite_bytes += guard_len;
                                        o += guard_len;
                                    }
                                    else
                                    {
                                        ssize_t guard_len = w - second_last_i32;
                                        ssize_t rest_len = second_last_i32 - last_loop;
                                        fprintf(stderr, "Found clean guard at: %ld [0x%lx] - %ld [0x%lx], "
                                                "moving to %ld [0x%lx] - %ld [0x%lx]\n", 
                                                second_last_i32 - wstart,
                                                second_last_i32 - wstart,
                                                w - wstart,
                                                w - wstart,
                                                last_loop - wstart,
                                                last_loop - wstart,
                                                last_loop - wstart + guard_len,
                                                last_loop - wstart + guard_len
                                            );

                                        // first move the instructions down
                                        memcpy(last_loop_out + guard_len, last_loop, rest_len);

                                        // then copy the guard into position
                                        memcpy(last_loop_out, second_last_i32, guard_len);

                                        // prevent moving a second guard here if somehow there is one
                                        last_loop = 0;
                                    }
                                }

                                RESET_GUARD_FINDER();
                                continue;
                            } else
                            if (ins == 0x10U)                       // call
                            {
                                REQUIRE(1);
                                uint8_t* ptr = w - 1;
                                uint64_t f = LEB();
                                if (f != guard_func_idx)
                                    RESET_GUARD_FINDER()
                                else
                                    call_guard_found = ptr;
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            } else                            
                            if (ins == 0x41U)                       // i32.const
                            {
                                REQUIRE(1);
                                second_last_i32 = last_i32;
                                last_i32 = w - 1;

                                second_last_i32_actual = last_i32_actual;

                                last_i32_actual = LEB();

                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                i32_found++;
                                continue;
                            } else
                            if (i32_found > 0)
                                between_const_and_guard++;


                            if (ins == 0x0EU)                       // br table
                            {
                                REQUIRE(1);
                                uint64_t vc = LEB();
                                for (int i = 0; i < vc; ++i)
                                {
                                    LEB();
                                }

                                LEB();
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;

                            }


                            // single byte instructions
                            if (ins == 0xD1U ||                     // is null
                                ins == 0x1BU ||                     // select
                                (ins >= 0x45U && ins <= 0xC4U) ||   // numeric single byte
                                ins == 0x0FU ||                     // return
                                ins == 0x00U ||                     // unreachable
                                ins == 0x01U ||                     // nop
                                ins == 0x05U ||                     // else
                                ins == 0x0BU)                       // end block
                            {
                                *o++ = ins;
                                continue;
                            }
                            
                            // single LEB instructions
                            if (ins == 0xD0U ||                     // ref.null
                                ins == 0xD2U ||                     // ref.func
                                (ins >= 0x20U && ins <= 0x24U) ||   // variable instructions
                                (ins == 0x25U || ins == 0x26U) ||   // table.get table.set
                                ins == 0x25U ||                     // table.get
                                ins == 0x26U ||                     // table.set
                                ins == 0x42U ||                     // i64.const
                                ins == 0xFCU ||                     // saturating instructions
                                ins == 0x0CU ||                     // br 
                                ins == 0x0DU)                       // br if
                            {
                                REQUIRE(1);
                                LEB();
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }

                            // double LEB instructions
                            if (ins == 0x11U)                       // call_indirect
                            {
                                REQUIRE(1);
                                LEB();
                                REQUIRE(1);
                                LEB();
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }

                            // vector of single byte types
                            if (ins == 0x1CU)                       // select t* 
                            {
                                REQUIRE(1);
                                uint64_t vec_count = LEB();
                                REQUIRE(vec_count);
                                ADVANCE(vec_count);
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }


                            // double byte instructions
                            if (ins == 0x3FU || ins == 0x40U)       // memory size, grow
                            {
                                REQUIRE(1);
                                ADVANCE(1);
                                *o++ = ins;
                                *o++ = 0x00U;
                                continue;
                            }

                            // f32 single float instructions
                            if (ins == 0x43U)                       // f32.const
                            {
                                REQUIRE(4);
                                ADVANCE(4);
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }
                            
                            // f64 single float instructions
                            if (ins == 0x44U)                       // f64.const
                            {
                                REQUIRE(8);
                                ADVANCE(8);
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }

                            // 0xFC instructions
                            if (ins == 0xFCU)
                            {
                                REQUIRE(1);
                                uint64_t t = LEB();
                                switch(t)
                                {
                                    case 8:                         // mem.init
                                    {
                                        LEB();
                                        REQUIRE(1);
                                        ADVANCE(1);
                                        break;
                                    }
                                    case 9:                         // data.drop
                                    {
                                        LEB();                  
                                        break;
                                    }
                                    case 10:                        // mem.copy
                                    {
                                        LEB();
                                        REQUIRE(2);
                                        ADVANCE(2);
                                        break;
                                    }
                                    case 11:                        // mem.fill
                                    {
                                        REQUIRE(1);
                                        ADVANCE(1);
                                        break;
                                    }
                                    default:
                                    {
                                        if (!(t >= 0 && t <= 7))
                                        return fprintf(stderr,
                                                "While processing 0xFC instr unknown type at: %ld\n",
                                                w-wstart);
                                    }
                                }
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }

                            // single memargs
                            if (ins >= 0x28U && ins <= 0x3EU)
                            {
                                REQUIRE(1);
                                LEB();
                                REQUIRE(1);
                                LEB();
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }


                            // vector instructions 
                            if (ins == 0xFDU)
                            {
                                REQUIRE(1);
                                uint64_t t = LEB(); 

                                // single memarg
                                if ((t >= 0 && t <= 11) ||
                                    (t == 92 || t == 93))
                                {
                                    LEB(); LEB();
                                }
                                else
                                // single memarg followed by a single byte
                                if (t >= 84 && t <= 91)
                                {
                                    LEB(); LEB(); 
                                    REQUIRE(1);
                                    ADVANCE(1);
                                }
                                else
                                // 16 byte arg
                                if (t == 12 || t == 13)
                                {
                                    REQUIRE(16);
                                    ADVANCE(16);
                                }
                                else
                                // single byte
                                if (t >= 21 && t <= 34)
                                {
                                    REQUIRE(1);
                                    ADVANCE(1);
                                }
                                else 
                                {
                                    // 0 byte instruction, do nothing
                                }
                                memcpy(o, instr_start, w-instr_start);
                                o += (w - instr_start);
                                continue;
                            }
                        }
                      
                        /*
                            int guard_rewrite_bytes = 0;
                            uint8_t* code_size_ptr = o;
                        */

                        fprintf(stderr, "Rewriting codesec from: %ld to %ld at %ld [0x%lx]\n",
                                code_size,
                                code_size + guard_rewrite_bytes,
                                code_size,
                                code_size);

                        leb_out_pad(code_size + guard_rewrite_bytes, /* 1 byte for vec len */
                                &code_size_ptr, 3);
                    }
                    else
                        ADVANCE(code_size);     // skip other functions
                }

                // rewrite the total size of the section
                fprintf(stderr, "Rewriting codesec section from: %ld to %ld at %ld [0x%lx] \n",
                        out_code_size + 1,
                        out_code_size + 1 + total_guard_rewrite_bytes,
                        out_code_size,
                        out_code_size);

                leb_out_pad(out_code_size + total_guard_rewrite_bytes + 1, /* 1 byte for vec len */
                        &codesec_out_size_ptr, 3);
                continue;
            }


            default:
            {
                ADVANCE(section_len);
                continue;
            }
        }

    }

    *len = (o - ostart);
    return 0; 
}


int run(char* fnin, char* fnout)
{
    if (strlen(fnin) == 0 || (fnout && strlen(fnout) == 0))
    {
        fprintf(stderr, "Invalid [blank] filenames\n");
        return 2;
    }

    // handle optional fnout
    if (fnout == 0)
        fnout = fnin;

    int fin = 0;
    off_t finlen = 0x100000U;

    if (strcmp(fnin, "-") != 0 && strcmp(fnin, "/dev/stdin") != 0)
    {
        // open wasm file
        fin = open(fnin, O_RDONLY);
        if (fin < 0)
            return fprintf(stderr, "Could not open file `%s` for reading\n", fnin);

        // get its length
        finlen = lseek(fin, 0L, SEEK_END);
        lseek(fin, 0L, SEEK_SET);
    }


    // create a buffer
    uint8_t* inp = (uint8_t*)malloc(finlen);
    if (!inp)
        return fprintf(stderr, "Could not allocate %ld bytes\n", finlen);
    
    // read file into buffer
    ssize_t upto = 0;
    while (upto < finlen)
    {
        ssize_t bytes_read = read(fin, inp + upto, fin == 0 ? 1 : (finlen - upto));
        upto += bytes_read;

        if (bytes_read < 0 || (fin != 0 && bytes_read == 0 && upto < finlen))
            return
                fprintf(stderr,
                    "Could not read all of file `%s`, only read %ld out of %ld bytes.\n",
                    fnin, upto, finlen);
        if (bytes_read == 0)
        {
            finlen = upto;
            break;
        }
    }

    fprintf(stderr, "Read source bytes: %ld out of %ld\n", upto, finlen);


    uint8_t* out = (uint8_t*)malloc(finlen * 2);
    if (!out)
        return fprintf(stderr, "Could not allocate %ld bytes\n", finlen);

    // done with fin
    close(fin);

    int fout = 1;

    if (strcmp(fnout, "-") != 0 && strcmp(fnout, "/dev/stdout") != 0)
    {
        // open output file
        fout = open(fnout, O_TRUNC | O_CREAT | O_WRONLY, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH);
        if (fout < 0)
            return fprintf(stderr, "Could not open file `%s` for writing\n", fnout);
    }

    // run cleaner
    ssize_t len = finlen;
    int retval = cleaner(inp, out, &len);

    // write output hook
    if (retval == 0)
    {
        ssize_t upto = 0;
        while (upto < len)
        {
            ssize_t bytes_written = write(fout, out + upto, len - upto);
            upto += bytes_written;
            if (bytes_written < 0 || (bytes_written == 0 && upto < len))
            {
                retval =
                    fprintf(stderr,
                    "Could not write all of output file `%s`, only wrote %ld out of %ld bytes. Check disk space.\n",
                    fnout, upto, len);
                break;
            }
        }
        fprintf(stderr, "Wrote output bytes: %ld out of %ld\n", upto, len);
    }
        
    // close output file
    close(fout);

    // free buffers
    free(inp);
    free(out);

    return retval;

}

int print_help(int argc, char** argv)
{
    fprintf(stderr, 
            "Hook Cleaner v" VERSION ". Richard Holland / XRPL-Labs 26/04/2022.\n"
            "Usage: %s in.wasm [out.wasm]\n"
            "Notes: If out.wasm is omitted then in.wasm is replaced.\n"
            "       Strips all functions and exports except cbak() and hook().\n"
            "       Also strips custom sections.\n"
            "       Specify - for stdin/out.\n", argv[0]);
    return 1;
}

int main(int argc, char** argv)
{
    if (argc == 2 && 
        ((strlen(argv[1]) >= 2 && argv[1][0] == '-' && argv[1][1] == 'h') ||
         (strlen(argv[1]) >= 3 && argv[1][0] == '-' && argv[1][1] == '-') && argv[1][2] == 'h'))
        return print_help(argc, argv);
    else if (argc == 2 || argc == 3)
        return run(argv[1], (argc == 2 ? 0 : argv[2]));
    else
        return print_help(argc, argv);
}
