
/*
 Different Straterigies Examined are:
 1. Write Back
 
 (---> {IF RD IS A MISS} --->Bring data in cache-->read data-->always bring entire block in cache--> Maintain LRU
 // Write Back ---> {IF RD IS A HIT } --->read data--> Maintain LRU 
 // Write Back ---> {IF WR IS A MISS} --->Bring data in cache-->write data-->always bring entire block in cache--> Maintain LRU 
 // Write Back ---> {IF WR IS A HIT } --->write data-->SET DIRTY BIT AS 1--> Maintain LRU )
 
 
 2.  WRITE THROUGH ALLOCATE
 
 {IF WR IS A MISS} --->Bring data in cache-->write to cache-->write to memory-->Maintain LRU
 {IF WR IS A HIT } --->write to cache-->write to memory-->Maintain LRU
 
 
 3. WRITE THROUGH NON ALLOCATE
 {IF WR IS A MISS} --->write to memory
 {IF WR IS A HIT } --->write to cache-->write to memory-->Maintain LRU
 
 Structure of Cache :
 MAX lines=262144 [L] == l=18
 MIN lines=4096 [L] == l=12
 MAX TAG SIZE= 18
 */


#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <complex>
#define complex std::complex<double>

#define MAX_TAG 27;
#define MAX_LRU 8 
#define CACHE_ALIGN __declspec(align(64))

uint32_t i, l, m;
uint32_t x[262144];
uint32_t bl;                    // [4] = { 1,2,4,8 };
uint32_t n;                     // as N[4] = { 1,2,4,8 } so n[4]={0,1,2,3}

uint32_t wr_strat;
uint32_t replacestrat;          // [2] = { 0,1 };


// Counters
uint32_t r_mem; //read memory
uint32_t r_line; //read line
uint32_t r_linehit; //read line hit 
uint32_t r_linedirty; //read line dirty
uint32_t r_linereplace; //Miss counter 

uint32_t w_mem; //write memory
uint32_t w_line; //write line
uint32_t w_linehit; //write line hit 
uint32_t w_linedirty; //write line dirty
uint32_t w_linereplace; //write counter
uint32_t write_through_mem;

uint32_t flush_dirty; //flush dirty count

//// CACHE STRUCTURE
uint32_t valid[65536][8];
uint32_t dirty[65536][8];
uint32_t tag[65536][8];
uint32_t lru[65536][8];
uint32_t replacecounter[655536][1];
uint32_t S = (256 * 1024);

void RBM() {
    uint32_t k;
    for (k = 0; k < 65536; k++)
        replacecounter[k][1] = 0;
}

uint32_t get_line(uint32_t add)
{
    uint32_t  b = 1, t, l;
    uint32_t line;
    
    uint32_t BL, B;
    BL = pow(2, bl);
    B = BL * 4;
    b = uint32_t(log(B) / log(2));
    
    uint32_t N, L;
    N = pow(2, n);
    L = S / (B * N);
    l = uint32_t(log(L) / log(2));
    
    t = 32 - l - b;
    
    line = ((add << t) >> (t + b));
    
    return (line);
}
uint32_t get_tag(uint32_t add)
{
    uint32_t b, l;
    uint32_t tag;
    
    uint32_t BL, B;
   BL = pow(2, bl);
    B = BL * 4;
    b = uint32_t(log(B) / log(2));
    
    uint32_t N, L;
    N = pow(2, n);
    L = S / B * N;  // N B 
    l = uint32_t(log(L) / log(2));
    
    tag = (add >> (b + l));
    //printf("Tag value is %d \n", tag);
    return (tag);
}
uint32_t getmsb(uint32_t add1) {
    uint32_t BL;
    BL = pow(2, bl);
    uint32_t addr;
    addr = (add1 / (BL * 4));
    return (addr);
}

uint32_t hitfunc(uint32_t line1, uint32_t tag1) {
    uint32_t line = line1;
    uint32_t hit = 0;
    uint32_t k;
    uint32_t N = (pow(2, n));
    for (k = 0; k <= (N - 1); k++) {
        if ((tag[line][k] == tag1) && (valid[line][k] == 1)) {
            hit = 1;
            break;
        }
        
    }
    return hit;
    
}

uint32_t updateLRU(uint32_t line1, uint32_t tag1) {
    uint32_t line = line1;
    uint32_t hit = 0;
    uint32_t k;
    uint32_t least_value = lru[line][0], temp1, temp2, least_value_index = 0;
    uint32_t N = (pow(2, n));
    for (k = 0; k <= (N - 1); k++) {
        if ((tag[line][k] == tag1) && (valid[line][k] == 1)) {
            hit = 1;
             break;
        }
        
    }
    
    if (hit == 1) {
        least_value_index = k;
        lru[line][k]++;
        lru[line][k]++;
        uint32_t N = (pow(2, n));
        for (k = 0; k <= (N - 1); k++) {
            if (lru[line][k] > 0) {
                lru[line][k]--;
            }
        }
    }
    
    if (hit == 0) {
        uint32_t N = (pow(2, n));
        if (N > 1) {
            for (k = 0; k < (N - 1); k++) {
                temp1 = lru[line][k];
                temp2 = lru[line][k + 1];
                
                if (temp1 < temp2) {
                    if (temp1 < least_value) {
                        least_value = temp1;
                        least_value_index = k;
                    }
                }
                else if (temp1 > temp2)
                {
                    if (temp2 < least_value) {
                        least_value = temp2;
                        least_value_index = k + 1;
                    }
                }
            }
            lru[line][least_value_index]++;
        }
    }
    
    return least_value_index;
    
}
void writeline(uint32_t line1, uint32_t tag1) {
    
    
    uint32_t line = line1;
    uint32_t hit = hitfunc(line1, tag1);
    uint32_t leastLruvalue;
    uint32_t replaceblock = replacecounter[line][1];
    
    if (hit == 1) {
        w_linehit++;
        if (wr_strat == 0 ) {
            
            leastLruvalue = updateLRU(line, tag1);
            tag[line][leastLruvalue] = tag1;
            valid[line][leastLruvalue] = 1;
            dirty[line1][leastLruvalue] = 1;
           
        }
        if (wr_strat == 1 || wr_strat == 2) {
            
            //rm++;
            leastLruvalue = updateLRU(line, tag1);
            tag[line][leastLruvalue] = tag1;
            valid[line][leastLruvalue] = 1;
            dirty[line1][leastLruvalue] = 0;
     
        }
    }
    
    
    else if (hit == 0 && wr_strat == 0 && replacestrat == 0 )
    {
        
        uint32_t leastLRUvalue = updateLRU(line, tag1);
        if (dirty[line][leastLRUvalue] == 1)
        {
             w_linedirty++;
            tag[line][leastLRUvalue] = tag1;
            valid[line][leastLRUvalue] = 1;
            dirty[line][leastLRUvalue] = 0;
            
            
            w_linereplace++;
            
        }
        else if (dirty[line][leastLRUvalue] == 0) {
            w_linereplace++;
            tag[line][leastLRUvalue] = tag1;
            valid[line][leastLRUvalue] = 1;
            dirty[line][leastLRUvalue] = 1;
        }
        
    }
    else if (hit == 0 && wr_strat == 0 && replacestrat == 1)
    {
        
        uint32_t N = (pow(2, n));
        if (dirty[line][replaceblock] == 1)
        {
            
            tag[line][replaceblock] = tag1;
            valid[line][replaceblock] = 1;
            dirty[line][replaceblock] = 0;
            w_linedirty++;
            replaceblock++;
            if (replaceblock == N )
                replaceblock = 0;
            
            replacecounter[line][1]= replaceblock;
            
            w_linereplace++;
        }
        
        else if (dirty[line][replaceblock] == 0) {
            
            tag[line][replaceblock] = tag1;
            valid[line][replaceblock] = 1;
            dirty[line][replaceblock] = 1;
            w_linedirty++;
            replaceblock++;
            if (replaceblock == N)
                replaceblock = 0;
            
            replacecounter[line][1] = replaceblock;
            w_linereplace++;
        }
        
    }
    else if ((hit == 0) && wr_strat == 1 && replacestrat == 0 ) {
        uint32_t leastLRUvalue = updateLRU(line, tag1);
        
        tag[line][leastLRUvalue] = tag1;
        valid[line][leastLRUvalue] = 1;
        dirty[line][leastLRUvalue] = 0;
        w_linereplace++;
    }
    else if ((hit == 0) && wr_strat == 1 && replacestrat == 1) {
        uint32_t N = (pow(2, n));
        
        tag[line][replaceblock] = tag1;
        valid[line][replaceblock] = 1;
        dirty[line][replaceblock] = 0;
        replaceblock++;
        if (replaceblock == N)
            replaceblock = 0;
        
        replacecounter[line][1] = replaceblock;
        
        w_linereplace++;
    }
    
    
}

void readLine(uint32_t line1, uint32_t tag1) {
    
    uint32_t line = line1;
    uint32_t replaceblock = replacecounter[line][1];
    uint32_t hit = hitfunc(line1, tag1);
    
    if ((hit == 1)) {
        r_linehit++;
        updateLRU(line, tag1);
    }
    else if ((hit == 0) && (replacestrat == 0))
    {
        
        
        uint32_t leastLRUvalue = updateLRU(line, tag1);
        uint32_t t = 1;
        
        
        if (valid[line][leastLRUvalue] == 1)
        {
            
            if (dirty[line][leastLRUvalue] == 1) {
                r_linedirty++;
                
                tag[line][leastLRUvalue] = tag1;
                valid[line][leastLRUvalue] = 1;
                dirty[line][leastLRUvalue] = 0;
                
                r_linereplace++;
                
                
            }
            else if (dirty[line][leastLRUvalue] == 0) {
                
                tag[line][leastLRUvalue] = tag1;
                valid[line][leastLRUvalue] = 1;
                dirty[line][leastLRUvalue] = 0;
                r_linereplace++;
                
            }
        }
        else if (valid[line][leastLRUvalue] == 0)
        {
            
            
            tag[line][leastLRUvalue] = tag1;
            valid[line][leastLRUvalue] = 1;
            dirty[line][leastLRUvalue] = 0;
            r_linereplace++;
        }
    }
    else if ((hit == 0) && (replacestrat == 1))
    {
        uint32_t N = (pow(2, n));
        if (valid[line][replaceblock] == 1)
        {
            if (dirty[line][replaceblock] == 1) {
                r_linedirty;	
                dirty[line][replaceblock] = 0;
                tag[line][replaceblock] = tag1;
                valid[line][replaceblock] = 1;
                replaceblock++;
                if (replaceblock == N)
                    replaceblock = 0;
                
                replacecounter[line][1] = replaceblock;
                r_linereplace++;
                
            }
            else if (dirty[line][replaceblock] == 0) {
                
                tag[line][replaceblock] = tag1;
                valid[line][replaceblock] = 1;
                dirty[line][replaceblock] = 0;
                replaceblock++;
                if (replaceblock == N)
                    replaceblock = 0;
                
                replacecounter[line][1] = replaceblock;
                r_linereplace++;
                
            }
            
        }
        else if (valid[line][replaceblock] == 0) {
            
            tag[line][replaceblock] = tag1;
            valid[line][replaceblock] = 1;
            if (wr_strat == 0)
                dirty[line][replaceblock] = 1;
            replaceblock++;
            if (replaceblock == N)
                replaceblock = 0;
            
            replacecounter[line][1] = replaceblock;
            
            r_linereplace++;
            
        }
    }
    
}

void readMemory(void* addr, uint32_t size)
{
    uint32_t tag, line;
    uint32_t addr32 = (uint32_t)addr;
    uint32_t oldLine = -1;
    r_mem++;
    for (int read_mem = 0; read_mem < size; read_mem++)
    {
        tag = get_tag(addr32 + read_mem);
        line = get_line(addr32 + read_mem);
        if (oldLine != line)
        {
            
            readLine(line, tag);
            r_line++;
            oldLine = line;
        }
    }
    
    
}


void writeMemory(void *addr, uint32_t size)
{
    uint32_t tag, line, most_significant_bits;
    uint32_t addr32 = (uint32_t)addr;     //aligned
    uint32_t oldLine = -1; 
    uint32_t oldmsb = -1; //oldMsb = -1;
    w_mem++;
    
    
    for (int write_mem = 0; write_mem < size; write_mem++)
    {
        tag = get_tag(addr32 + write_mem);
        line = get_line(addr32 + write_mem);
        if ((wr_strat == 1) || (wr_strat == 2))
        {
            most_significant_bits = getmsb(addr32 + i);
            if (most_significant_bits != oldmsb) {
                write_through_mem++;
                oldmsb = most_significant_bits;
            }
        }
        if (oldLine != line)
        {
            
            writeline(line, tag);
            oldLine = line;
            w_line++;
        }
    }

}
void clearcache() {
    uint32_t k, j;
    uint32_t N = (pow(2, n));
    for (k = 0; k < 65536; k++) {
        for (j = 0; j < (N - 1); j++) {
            valid[k][j] = 0;
            dirty[k][j] = 0;
            tag[k][j] = 0;
            lru[k][j] = 0;
        }
        
    }
    r_mem = 0;
    r_line = 0;
    r_linehit = 0;
    r_linedirty = 0;
    r_linereplace = 0;
    
    w_mem = 0;
    w_line = 0;
    w_linehit = 0;
    w_linedirty = 0;
    w_linereplace = 0;
    
    flush_dirty = 0;
    
}
void flush_cache()
{
    int k;
    uint32_t j;
    for (k = 0; k < 65536; k++)
    {
        for (j = 0; j < 8 ; j++)
        {
            if (dirty[k][j] == 1)
            {
                dirty[k][j] == 0;
                flush_dirty++;
                //wm++;
            }
        }
    }
    
}
void Radix2FFT(complex data[], int nPoints, int nBits)
{
    // cooley-tukey radix-2, twiddle factor
    // adapted from Fortran code from Burrus, 1983
    #pragma warning (disable: 4270)
    int i, j, k, l;
    int nPoints1, nPoints2;
    complex cTemp, cTemp2;
    
    double  dCos=1, dSin=0;
    
    readMemory(&nPoints, sizeof(nPoints));
    writeMemory(&nPoints2, sizeof(nPoints2));
    nPoints2 = nPoints;
    
    writeMemory(&k, sizeof(k));
    readMemory(&k, sizeof(k));
    readMemory(&nBits, sizeof(nBits));
    
    for (k = 1; k <= nBits; k++)
    {
        
        readMemory(&nPoints2, sizeof(nPoints2));
        writeMemory(&nPoints1, sizeof(nPoints1));
        nPoints1 = nPoints2;
        
        readMemory(&nPoints2, sizeof(nPoints2));
        writeMemory(&nPoints2, sizeof(nPoints2));
        nPoints2 /= 2;
        // Compute differential angles
        double dTheta = 2 * 3.14159257 / nPoints1;
        readMemory(&nPoints1, sizeof(nPoints1));
        writeMemory(&dTheta, sizeof(dTheta));
        
        double dDeltaCos = cos(dTheta);
        readMemory(&dTheta, sizeof(dTheta));
        writeMemory(&dDeltaCos, sizeof(dDeltaCos));
        
        double dDeltaSin = sin(dTheta);
        readMemory(&dTheta, sizeof(dTheta));
        writeMemory(&dDeltaSin, sizeof(dDeltaSin));
        
        
        // Initialize angles
        
        writeMemory(&dCos, sizeof(dCos));
        writeMemory(&dSin, sizeof(dSin));
        double dCos = 1;
        double dSin = 0;
        // Perform in-place FFT
        
        writeMemory(&j, sizeof(j));
        readMemory(&j, sizeof(j));
        readMemory(&nPoints2, sizeof(nPoints2));
        
        for (j = 0; j < nPoints2; j++)
        {
            readMemory(&j, sizeof(j));
            writeMemory(&i, sizeof(i));
            i = j;
            
            readMemory(&i, sizeof(i));
            readMemory(&nPoints, sizeof(nPoints));
            while (i < nPoints)
            {
                
                readMemory(&i, sizeof(i));
                readMemory(&nPoints2, sizeof(nPoints2));
                writeMemory(&l, sizeof(l));
                l = i + nPoints2;
                
                readMemory(&i, sizeof(i));
                readMemory(&data[i], sizeof(data[i]));
                readMemory(&i, sizeof(l));
                readMemory(&data[l], sizeof(data[l]));
                
                readMemory(&i, sizeof(i));
                readMemory(&data[i], sizeof(data[i]));
                readMemory(&i, sizeof(l));
                readMemory(&data[l], sizeof(data[l]));
                
                writeMemory(&cTemp, sizeof(cTemp));
                writeMemory(&cTemp2, sizeof(cTemp2));
                cTemp = data[i] - data[l];
                cTemp2 = data[i] + data[l];
                
                data[i] = cTemp2;
                readMemory(&cTemp2, sizeof(cTemp2));
                readMemory(&i, sizeof(i));
                writeMemory(&data[i], sizeof(data[i]));
                
                
                readMemory(&dCos, sizeof(dCos));
                readMemory(&cTemp, sizeof(cTemp));
                readMemory(&dSin, sizeof(dSin));
                readMemory(&cTemp, sizeof(cTemp));
                writeMemory(&cTemp2, sizeof(cTemp2));
                cTemp2 = complex(dCos * cTemp.real() + dSin * cTemp.imag(),
                                 
                                 dCos * cTemp.imag() - dSin * cTemp.real());
                
                readMemory(&cTemp2, sizeof(cTemp2));
                readMemory(&l, sizeof(l));
                writeMemory(&data[l], sizeof(data[l]));
                data[l] = cTemp2;
                
                readMemory(&nPoints1, sizeof(nPoints1));
                readMemory(&i, sizeof(i));
                writeMemory(&i, sizeof(i));
                i += nPoints1;
            }
            double dTemp = dCos;
            readMemory(&dCos, sizeof(dCos));
            writeMemory(&dTemp, sizeof(dTemp));
            
            dCos = dCos * dDeltaCos - dSin * dDeltaSin;
            readMemory(&dCos, sizeof(dCos));
            readMemory(&dDeltaCos, sizeof(dDeltaCos));
            readMemory(&dSin, sizeof(dSin));
            readMemory(&dDeltaSin, sizeof(dDeltaSin));
            writeMemory(&dCos, sizeof(dCos));
            
            
            dSin = dTemp * dDeltaSin + dSin * dDeltaCos;
            readMemory(&dTemp, sizeof(dTemp));
            readMemory(&dDeltaCos, sizeof(dDeltaCos));
            readMemory(&dSin, sizeof(dSin));
            readMemory(&dDeltaSin, sizeof(dDeltaSin));
            writeMemory(&dSin, sizeof(dSin));
            
            
            //2nd for loop :j++
            readMemory(&j, sizeof(j));
            readMemory(&nPoints2, sizeof(nPoints2));
            writeMemory(&j, sizeof(j));
            
        }
        
        //1st for loop : k++
        readMemory(&k, sizeof(k));
        readMemory(&nBits, sizeof(nBits));
        writeMemory(&k, sizeof(k));
        
    }
    
    // Convert Bit Reverse Order to Normal Ordering
    writeMemory(&j, sizeof(j));
    j = 0;
    
    readMemory(&nPoints, sizeof(nPoints));
    writeMemory(&nPoints1, sizeof(nPoints1));
    nPoints1 = nPoints - 1;
    
    writeMemory(&i, sizeof(i));
    readMemory(&i, sizeof(i));
    readMemory(&nPoints1, sizeof(nPoints1));
    for (i = 0; i < nPoints1; i++)
    {
        readMemory(&i, sizeof(i));
        readMemory(&j, sizeof(j));
        if (i < j)
        {
            readMemory(&j, sizeof(j));
            readMemory(&data[j], sizeof(data[j]));
            writeMemory(&cTemp, sizeof(cTemp));
            cTemp = data[j];
            
            readMemory(&i, sizeof(i));
            readMemory(&data[i], sizeof(data[i]));
            writeMemory(&cTemp2, sizeof(cTemp2));
            cTemp2 = data[i];
            
            readMemory(&cTemp, sizeof(cTemp));
            readMemory(&i, sizeof(i));
            writeMemory(&data[i], sizeof(data[i]));
            data[i] = cTemp;
            
            readMemory(&cTemp2, sizeof(cTemp2));
            readMemory(&j, sizeof(j));
            writeMemory(&data[j], sizeof(data[j]));
            data[j] = cTemp2;
            readMemory(&i, sizeof(i));
            readMemory(&j, sizeof(j));
        }
        
        readMemory(&nPoints, sizeof(nPoints));
        writeMemory(&k, sizeof(k));
        k = nPoints / 2;
        
        readMemory(&k, sizeof(k));
        readMemory(&j, sizeof(j));
        while (k <= j)
        {
            readMemory(&j, sizeof(j));
            readMemory(&k, sizeof(k));
            writeMemory(&j, sizeof(j));
            j -= k;
            
            readMemory(&k, sizeof(k));
            writeMemory(&k, sizeof(k));
            k /= 2;
            readMemory(&k, sizeof(k));
            readMemory(&j, sizeof(j));
        }
        
        readMemory(&j, sizeof(j));
        readMemory(&k, sizeof(k));
        writeMemory(&j, sizeof(j));
        j += k;
        
        //i++
        readMemory(&i, sizeof(i));
        readMemory(&nPoints1, sizeof(nPoints1));
        writeMemory(&i, sizeof(i));
    }
    
#pragma warning(default: 4270)
}
void Xl_display_setup(){
    FILE *count;
    count = fopen("C:\\Users\\APAAR\\Desktop\\cache_data.xls", "w");
    if (count == NULL)
    {
        fprintf(stderr, "can't open file!\n");
        exit(1);
    }
    //	fprintf(count, "Strategy 0: Write Back, 1:Write Through Alocate, 2: Write Through Non-Allocate\n");
    fprintf(count, "wr_strat\tn\tbl\treplace_strat\tRead Line\tRead Line Hit\tRead Memory\tRead Line Replace\tRead Line Dirty\tWrite Line\tWrite Line Hit\tWrite Line Replace\tWrite Memory\tWrite Line Dirty\tWrite Through Count\tFlush Dirty\tTime\tRank\n");
    fclose(count);
}
void XL_display_end() {
    FILE *count;
    count = fopen("C:\\Users\\APAAR\\Desktop\\cache_data.xls", "a");
    if (count == NULL)
    {
        fprintf(stderr, "can't open file!\n");
        exit(1);
    }
    
    fprintf(count, "%d\t", wr_strat);
    fprintf(count, "%d\t", n);
    fprintf(count, "%d\t", bl);
    fprintf(count, "%d\t", replacestrat);
    fprintf(count, "%d\t", r_line);
    fprintf(count, "%d\t", r_linehit);
    fprintf(count, "%d\t", r_mem);
    fprintf(count, "%d\t", r_linereplace);
    fprintf(count, "%d\t", r_linedirty);
    fprintf(count, "%d\t", w_line);
    fprintf(count, "%d\t", w_linehit);
    fprintf(count, "%d\t", w_linereplace);
    fprintf(count, "%d\t", w_mem);
    fprintf(count, "%d\t", w_linedirty);
    fprintf(count, "%d\t", write_through_mem);
    fprintf(count, "%d\t", flush_dirty);
    
    uint32_t BL = BL = pow(2, bl);
    
    uint32_t T =( ((r_linedirty + r_linereplace)*(90 + 15 * (BL - 1))) + (r_linehit * 1) + (w_linehit * 1) +
                 ((w_linedirty + w_linereplace)*(90 + 15 * (BL - 1)))  + (write_through_mem * 90) + (flush_dirty * 90)  );
    
    fprintf(count, "%u\t\n", T);
    
    fclose(count);
}





int main(int argc, char* argv[])// the parameters inside main.. i ll remove.. i dnt need them... these camefrom here.. see 
{
    RBM();
    Xl_display_setup();
    int i;
    CACHE_ALIGN complex data[32768];
    
    int points = 32768;
    printf("FFT Test App\r\n");
    // time domain: zero-offset real cosine function
    // freq domain: delta fn with zero phase
#define cycles 1 // max cycles is points/2 for Nyquist
    for (i = 0; i < points; i++)
        data[i] = complex(cos(2.0*3.1416*float(i) / float(points)*cycles), 0.0);
    /*
     // time domain: impulse time offset
     // freq domain: constant amplitude of 1
     // phase is zero for zero time offset
     // 1 phase rotation per unit time offset
     #define DELTA_T 0
     for (i = 0; i < points; i++)
     data[i] = complex(0.0, 0.0);
     data[DELTA_T] = complex(1.0, 0.0);
     */
    int bits = ceil(log(points) / log(2));
    for (wr_strat = 0; wr_strat <= 2; wr_strat++) {
        for (n = 0; n <= 3; n++) {
            for (bl = 0; bl <= 3; bl++) {
                for (replacestrat = 0; replacestrat <= 1; replacestrat++) {
                    
                    clearcache();
                    Radix2FFT(data, points, bits);
                    flush_cache();
                    XL_display_end();
                    
                }
            }
        }
    }
    
    for (i = 0; i < points; i++)
        if (data[i].imag() >= 0.0)
            printf("x[%d] = %2.4lf + j%2.4lf\n", i,
                   data[i].real(), data[i].imag());
        else
            printf("x[%d] = %2.4lf - j%2.4lf\n", i,
                   data[i].real(), -data[i].imag());
    return 0;
} 
