#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdlib.h>

#define VERSION "1.0"
#define DEBUG 1
#define DEBUG_VERBOSE 0

#define MAX_TYPES 256
#define MAX_FUNCS 256   /* this includes imports! */

uint64_t leb(
    uint8_t** buf,
    uint8_t* bufend)
{
    uint64_t val = 0, shift = 0, i = 0;
    while (*buf + i < bufend)
    {
        int b = (int)((*buf)[i]);
        uint64_t last = val;
        val += (b & 0x7F) << shift;
        if (val < last)
        {
            fprintf(stderr, "LEB128 overflow in input wasm at offset %ld.\n",
                    i);
            exit(100);
        }
        ++i;
        if (b & 0x80)
        {
            shift += 7;
            continue;
        }
        *buf += i;
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

int cleaner (
    uint8_t*    w,      // web assembly input buffer
    uint8_t*    o,      // web assembly output buffer
    ssize_t*    len)    // length of input buffer when called, and len of output buffer when returned
{
    // require at least `need` bytes
    #define REQUIRE(need)\
    {\
        if (DEBUG && DEBUG_VERBOSE)\
            printf("Require %ld b\tfrom 0x%lX to 0x%lX\n",\
                ((uint64_t)(need)),\
                ((uint64_t)(w-wstart)),\
                ((uint64_t)(w+need-wstart)));\
        if (wlen - (w - wstart) < need)\
            return \
                fprintf(stderr,\
                    "Truncated web assembly input. SrcLine: %d. Illegally short at position %ld.\n"\
                    "wlen: %ld w-wstart: %ld need:%ld\n"\
                    "%08lX : %02X %02X %02X %02X\n",\
                    __LINE__,\
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
            printf("Advance %ld b\tfrom 0x%lX to 0x%lX\n",\
                ((uint64_t)(adv)),\
                ((uint64_t)(w-wstart)),\
                ((uint64_t)(w+adv-wstart)));\
        w += adv;\
        REQUIRE(0);\
    }

    
    #define LEB()\
        (tmp2=w-wstart,tmp=leb(&w, wend),\
        (DEBUG && DEBUG_VERBOSE &&\
        printf("Leb read at 0x%lX: %ld\n", tmp2, tmp)),tmp)


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
        printf("First pass start\n");

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

    while (w < wend)
    {
        REQUIRE(1);
        uint8_t section_type = w[0];
        ADVANCE(1);

        uint64_t section_len = LEB();

        if (DEBUG)
            printf("Section type: %d, Section len: %ld, Section offset: 0x%lX\n",
                section_type, section_len, w - wstart);

        REQUIRE(section_len);

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

                        if (result_type = 0x7EU && result_count == 1 && is_P32)
                        {
                            if (DEBUG)
                                printf("Hook/Cbak type: %d\n", i);
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
                    printf("Import count: %d\n", out_import_count);

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
                    ADVANCE(name_length);

                    REQUIRE(1);
                    uint8_t import_type = w[0];
                    ADVANCE(1);

                    uint64_t import_idx = LEB();

                    if (import_type == 0x00)
                    {
                        if (DEBUG)
                            printf("Import %d type %ld\n",
                                func_upto, import_idx);
                        func_type[func_upto++] = import_idx;
                        out_import_size += (w - import_start);
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
                    printf("Function count: %d\n", func_count);
                for (int i = 0; i < func_count; ++i)
                {
                    func_type[out_import_count + i] = LEB();
                    if (DEBUG)
                        printf("Func %d is type %d\n",
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

    printf("hook idx: %d, cbak idx: %d\n", func_hook, func_cbak);

    // reset to top
    w = wstart;

    // pass two: write out
    
    if (DEBUG)
        printf("Second pass start\n");

    uint8_t* ostart = o;

    // magic number and version: 8 bytes
    for (int i = 0; i < 8; ++i)
        *o++ = *w++;

    while (w < wend)
    {
        REQUIRE(1);
        uint8_t section_type = w[0];
        ADVANCE(1);

        uint64_t section_len = LEB();

        if (DEBUG)
            printf("Section type: %d, Section len: %ld, Section offset: 0x%lX\n",
                section_type, section_len, w - wstart);

        REQUIRE(section_len);

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
                        if (func_type[i] == hook_cbak_type)
                        {
                            imports_use_hook_cbak_type = 1;
                            hook_cbak_type = type_count-1;
                        }
                    }
                }
                
                if (!imports_use_hook_cbak_type)
                {
                    hook_cbak_type = type_count++;
                    section_size += 5U;
                }
                
                if (type_count > 127*127)
                    return fprintf(stderr, "Too many types in wasm!\n");

                // account for the type vector size bytes
                section_size += (type_count > 127 ? 2U : 1U);

                if (DEBUG)
                    printf("type section_size: %d\n", section_size);
                // write out section size
                leb_out(section_size, &o);


                uint8_t* out_start = o;

                // write type vector len
                leb_out(type_count, &o);

                // write out types
                memset(used, 0, MAX_TYPES);
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
                    printf("actual len: %d\n", o - out_start);
                continue;
            }

            case 0x02U: // imports
            {
                *o++ = 0x02U;

                leb_out(out_import_size, &o);
                leb_out(out_import_count, &o);

                // only copy function imports
                int count = LEB();

                for (int i = 0; i < count; ++i)
                {
                    uint8_t* import_start = w;

                    // module name
                    int mod_length = LEB();
                    REQUIRE(mod_length);
                    ADVANCE(mod_length);

                    // import name
                    int name_length = LEB();
                    REQUIRE(name_length);
                    ADVANCE(name_length);

                    REQUIRE(1);
                    uint8_t import_type = w[0];
                    ADVANCE(1);

                    uint64_t import_idx = LEB();

                    if (import_type == 0x00)
                    {
                        int import_len = w-import_start;
                        memcpy(o, import_start, import_len);
                        o += import_len;
                    }
                    continue;
                }
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
                leb_out(s, &o); // sections size
                *o++ = (func_cbak == -1 ? 0x01U : 0x02U);   // vector size
                leb_out(hook_cbak_type, &o);    // vector entries
                leb_out(hook_cbak_type, &o);
                ADVANCE(section_len);
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
                    printf("Output code size: %ld\n", out_code_size + 1);

                leb_out(out_code_size + 1 /* allow for vec len */, &o);

                *o++ = (func_cbak == -1 ? 0x01U : 0x02U); // vec len

                uint64_t count = LEB();
                for (uint64_t i = 0; i < count; ++i)
                {
                    uint8_t* code_start = w;
                    uint64_t code_size = LEB();
                    ADVANCE(code_size);
                    if (i == (func_hook - out_import_count) || i == (func_cbak - out_import_count))
                    {
                        memcpy(o, code_start, w-code_start);
                        o += (w-code_start);
                    }
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

    // open wasm file
    int fin = open(fnin, O_RDONLY);
    if (fin < 0)
        return fprintf(stderr, "Could not open file `%s` for reading\n", fnin);

    // get its length
    off_t finlen = lseek(fin, 0L, SEEK_END);
    lseek(fin, 0L, SEEK_SET);

    // create a buffer
    uint8_t* inp = (uint8_t*)malloc(finlen);
    if (!inp)
        return fprintf(stderr, "Could not allocate %ld bytes\n", finlen);

    uint8_t* out = (uint8_t*)malloc(finlen);
    if (!out)
        return fprintf(stderr, "Could not allocate %ld bytes\n", finlen);

    // read file into buffer
    ssize_t upto = 0;
    while (upto < finlen)
    {
        ssize_t bytes_read = read(fin, inp + upto, finlen - upto);
        upto += bytes_read;

        if (bytes_read < 0 || (bytes_read == 0 && upto < finlen))
            return
                fprintf(stderr,
                    "Could not read all of file `%s`, only read %ld out of %ld bytes.\n",
                    fnin, upto, finlen);
    }

    printf("read bytes: %ld out of %ld\n", upto, finlen);

    // done with fin
    close(fin);

    // open output file
    int fout = open(fnout, O_TRUNC | O_CREAT | O_WRONLY);
    if (fout < 0)
        return fprintf(stderr, "Could not open file `%s` for writing\n", fnout);

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
                retval =fprintf(stderr,
                    "Could not write all of output file `%s`, only wrote %ld out of %ld bytes. Check disk space.\n",
                    fnout, upto, len);
                break;
            }
        }

        printf("wrote bytes: %ld out of %ld\n", upto, len);
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
            "       Also strips custom sections.\n", argv[0]);
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
