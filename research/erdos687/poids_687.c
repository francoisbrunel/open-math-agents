/* Find candidate dual weights. A separate exact integer check accepts them. */
/* The portable Lean/clang toolchain on Windows supplies the C runtime
   libraries without their headers. Use the ABI's own size type there. */
#if defined(_WIN32) && !__has_include(<math.h>)
typedef __SIZE_TYPE__ size_t;
extern double exp(double);
extern double pow(double, double);
extern void *malloc(size_t);
extern void *calloc(size_t,size_t);
extern void free(void *);
extern void *memset(void *,int,size_t);
#else
#include <math.h>
#include <stdlib.h>
#include <string.h>
#endif
#ifdef _WIN32
#define EXPORT __declspec(dllexport)
#else
#define EXPORT
#endif

EXPORT double search_weights(int n, int k, const int *primes, const int *points,
        int iterations, double goal, double *best) {
    int total = 0;
    for (int i = 0; i < k; ++i) total += primes[i];
    int *rows = malloc((size_t)n*k*sizeof *rows);
    int *hits = malloc(n*sizeof *hits);
    double *bins = malloc(total*sizeof *bins);
    double *w = malloc(n*sizeof *w);
    double *avg = calloc(n,sizeof *avg);
    double *factor = malloc((k+1)*sizeof *factor);
    if (!rows || !hits || !bins || !w || !avg || !factor) {
        free(rows); free(hits); free(bins); free(w); free(avg); free(factor);
        return 10;
    }
    for (int i = 0, offset=0; i<k; offset+=primes[i++]) {
        int p = primes[i];
        for (int j=0;j<n;++j) {
            int r = points[j]%p;
            rows[i*n+j] = offset+(r<0?r+p:r);
        }
    }
    double record=10, sum=0;
    for (int j=0;j<n;++j) { w[j]=best[j]>.0001?best[j]:.0001; sum+=w[j]; }
    int averages=0;
    for (int step=0;step<iterations;++step) {
        if (step==75 || step==300 || step==900) {
            memset(avg,0,n*sizeof *avg);
            averages=0;
        }
        for (int j=0;j<n;++j) avg[j]+=w[j]/sum;
        ++averages;
        int averaging = (step%25==24);
        double *current = averaging ? avg : w;
        double denom = averaging ? averages : sum;
        memset(bins,0,total*sizeof *bins);
        memset(hits,0,n*sizeof *hits);
        double maxsum=0;
        for (int i=0,offset=0;i<k;offset+=primes[i++]) {
            int *row=rows+i*n;
            for (int j=0;j<n;++j) bins[row[j]]+=current[j];
            int largest=offset;
            for(int c=offset+1;c<offset+primes[i];++c)
                if(bins[c]>bins[largest]) largest=c;
            maxsum+=bins[largest];
            for(int j=0;j<n;++j) hits[j]+=(row[j]==largest);
        }
        double ratio=maxsum/denom;
        if(ratio<record) {
            record=ratio;
            for(int j=0;j<n;++j) best[j]=n*current[j]/denom;
            if(record<goal) break;
        }
        double rate=.40/pow(1+step/12.0,.55);
        if (averaging) rate*=.25;
        factor[0]=exp(rate);
        double shrink=exp(-rate);
        for(int v=1;v<=k;++v)factor[v]=factor[v-1]*shrink;
        sum=0;
        for(int j=0;j<n;++j) { w[j]*=factor[hits[j]]; sum+=w[j]; }
        if(sum>1e20 || sum<1e-20) {
            for(int j=0;j<n;++j) w[j]*=n/sum;
            sum=n;
        }
    }
    free(rows);free(hits);free(bins);free(w);free(avg);free(factor);
    return record;
}
