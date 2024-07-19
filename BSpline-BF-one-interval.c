//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%                                                                          %%
//%%                                                    Wroc{\l}aw, July 2024 %%
//%%                                                                          %%
//%%                                                                          %%
//%%                                                                          %%
//%%          EFFICIENT EVALUATION OF BERNSTEIN-BEZIER COEFFICIENTS           %%
//%%             OF B-SPLINE BASIS FUNCTIONS OVER ONE KNOT SPAN               %%
//%%                               (test program)                             %%
//%%                                                                          %%
//%%                                 GCC 13.2.0                               %%
//%%                                                                          %%
//%%                                                                          %%
//%%                     Filip Chudy, Pawe{\l} Wo\'{z}ny                      %%
//%%                                                                          %%
//%%                                                                          %%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


#include<stdio.h>
#include<stdlib.h>
#include<time.h>
#include<math.h>

void generate_knots(int m, int n, double* knots, double start_left, double start_right, double max_eps)
{
    int knots_max = 2 * m + n + 1;
    int known_knots = 0;
    double knot = start_left + (rand() / (double) RAND_MAX) * (start_right - start_left);
    while(known_knots < knots_max)
    {
        int multiplicity = 1 + rand() % (m + 1);
        double knot_eps = (rand() / (double) RAND_MAX) * max_eps;
        while(knot_eps <= 0.0) knot_eps = (rand() / (double) RAND_MAX) * max_eps;
        if(known_knots + multiplicity > knots_max) multiplicity = knots_max - known_knots;
        knot += knot_eps;
        for(int final_knots = known_knots + multiplicity; known_knots < final_knots; known_knots++)
        {
            knots[known_knots] = knot;
        }
    }
}

double min_log_abs(double x)
{
    if(x < 0.) x *= -1.;
    return -log10(x);
}

double get_digits(double a, double b, double max)
{
    double result;
    if(b == 0.0 && a == 0.0) return max;
    else if(b == 0.0) result = min_log_abs(a);
    else if(a == 0.0) result = min_log_abs(b);
    else result = min_log_abs((a - b) / b);

    if(result > max) return max;
    if(result < 0.) return 0.;
    return result;
}


void coefficients_deboor(int m, int n, int j, double* t, double* result)
{
    double b[m + 1][m + 1][m + 1];
    for(int p = 0; p <= m; p++)
    {
        for(int d = 0; d <= m; d++)
        {
            for(int k = 0; k <= m; k++) b[p][d][k] = 0.0;
        }
    }
    b[0][0][0] = 1.0;
    for(int p = 1; p <= m; p++)
    {
        double d1 = t[m + p + j] - t[m + j];
        double a3;
        if(d1 == 0.0) a3 = 0.0;
        else a3 = (t[m + j + 1] - t[m + j]) / d1;
        // k = 0
        b[p][0][0] = 0.0;
        for(int k = 1; k < p; k++)
        {
            b[p][0][k] = k * (a3 * b[p - 1][0][k - 1]) / p;
        }
        //k = p
        b[p][0][p] = a3 * b[p - 1][0][p - 1];

        for(int d = 1; d <= p; d++)
        {
            double d1 = t[m + p + j - d] - t[m + j - d];
            double d2 = t[m + p + j - d + 1] - t[m + j - d + 1];
            double a1, a2, a3, a4;
            if(d1 == 0.0)
            {
                a1 = 0.0;
                a3 = 0.0;
            }
            else
            {
                a1 = (t[m + j] - t[m + j - d]) / d1;
                a3 = (t[m + j + 1] - t[m + j - d]) / d1;
            }
            if(d2 == 0.0)
            {
                a2 = 0.0;
                a4 = 0.0;
            }
            else
            {
                a2 = (t[m + p + j - d + 1] - t[m + j]) / d2;
                a4 = (t[m + p + j - d + 1] - t[m + j + 1]) / d2;
            }
            // k = 0
            b[p][d][0] = a1 * b[p - 1][d][0] + a2 * b[p - 1][d - 1][0];
            for(int k = 1; k < p; k++)
            {
                b[p][d][k] = ((p - k) * (a1 * b[p - 1][d][k] + a2 * b[p - 1][d - 1][k])
                    + k * (a3 * b[p - 1][d][k - 1] + a4 * b[p - 1][d - 1][k - 1])) / p;
            }
            //k = p
            b[p][d][p] = a3 * b[p - 1][d][p - 1] + a4 * b[p - 1][d - 1][p - 1];
        }
    }

    int idx = 0;
    for(int k = 0; k <= m; k++)
    {
        for(int d = m; d >= 0; d--)
        {
            result[idx] = b[m][d][k];
            idx++;
        }
    }
}



void coefficients_new(int m, int n, int j, double* t, double* result)
{
    double bm[m + 1][m + 1];
    for(int i = 0; i <= m; i++) for(int j = 0; j <= m; j++) bm[i][j] = 0.0;

    bm[0][0] = 1.0;

    for(int p = 1; p <= m; p++)
    {
        double a = (t[m + j + 1] - t[m + j]) / (t[m + j + p] - t[m + j]);
        bm[p][0] = a * bm[p - 1][0];
    }
    for(int p = 1; p <= m; p++)
    {
        for(int d = 1; d <= p; d++)
        {
            double d1 = t[m + p + j - d] - t[m + j - d];
            double d2 = t[m + p + j - d + 1] - t[m + j - d + 1];
            double a1, a2, a3, a4;
            if(d1 == 0.0)
            {
                a1 = 0.0;
                a3 = 0.0;
            }
            else
            {
                a1 = (t[m + j] - t[m + j - d]) / d1;
                a3 = (t[m + j + 1] - t[m + j - d]) / d1;
            }
            if(d2 == 0.0)
            {
                a2 = 0.0;
                a4 = 0.0;
            }
            else
            {
                a2 = (t[m + p + j - d + 1] - t[m + j]) / d2;
                a4 = (t[m + p + j - d + 1] - t[m + j + 1]) / d2;
            }
            bm[p][d] = a3 * bm[p - 1][d] + a4 * bm[p - 1][d - 1];
        }
    }

    double b[m + 1][m + 1];
    for(int i = 0; i <= m; i++) for(int j = 0; j <= m; j++) b[i][j] = 0.0;
    b[0][m] = 1.0;
    for(int k = 2; k <= m; k++) b[0][m] *= (t[m + j + 1] - t[m + j]) / (t[m + j + 1] - t[m + j - k + 1]);
    for(int d = 0; d <= m; d++) b[m][d] = bm[m][d];
    for(int k = m - 1; k >= 0; k--)
    {
        for(int d = 1; d < m; d++)
        {
            double v = (t[2 * m + j - d + 1] - t[m + j - d]) / (t[2 * m + j - d + 2] - t[m + j - d + 1]);
            double a1 = t[m + j + 1] - t[2 * m + j - d + 2];
            double a2 = t[2 * m + j - d + 2] - t[m + j];
            double c1 = a1 * b[k][d - 1] + a2 * b[k + 1][d - 1];
            double c2 = (t[m + j] - t[m + j - d]) / (t[m + j + 1] - t[m + j - d]);
            b[k][d] = c2 * b[k + 1][d] + v * c1 / (t[m + j + 1] - t[m + j - d]);
        }
    }

    int idx = 0;
    for(int k = 0; k <= m; k++)
    {
        for(int d = m; d >= 0; d--)
        {
            result[idx] = b[k][d];
            idx++;
        }
    }
}

void coefficients_multi(int m, int n, int j, double* t, double* result)
{
    int skip_size = 0;
    double v, c1, c2, c3;
    double new_coeffs[m + 1][m + 1], old_coeffs[m + 1][m + 1];
    for(int i = 0; i <= m; i++) for(int k = 0; k <= m; k++) new_coeffs[i][k] = 0.;
    float numerator = pow(t[n + m] - t[n - 1 + m], m - 1);
    new_coeffs[m][m] = numerator;
    for(int k = 2; k <= m; k++)
        new_coeffs[m][m] /= t[n - 1 + k + m] - t[n - 1 + m];
    new_coeffs[0][0] = numerator;
    for(int k = 2; k <= m; k++)
        new_coeffs[0][0] /= t[n + m] - t[n - k + m];
    for(int i = n - 2; i >= n - m; i--)
    {
        c1 = (t[n - 1 + m] - t[i + m]) / (t[n + m] - t[i + m]);
        c2 = (t[n + m] - t[n - 1 + m])
            / (t[n + m] - t[i + 1 + m]);
        for(int k = m - 1; k >= 0; k--)
            new_coeffs[i + m - n + 1][k] = c1 * new_coeffs[i + m - n + 1][k + 1]
                + c2 * new_coeffs[i + m + 1 - n + 1][k + 1];
    }

    if(n - 1 > j)
    {
        for(int i = 0; i <= m; i++) for(int k = 0; k <= m; k++) old_coeffs[i][k] = new_coeffs[i][k];
        for(int i = 0; i <= m; i++) for(int k = 0; k <= m; k++) new_coeffs[i][k] = 0.;
    }

    for(int iter = n - 2; iter >= j; iter--)
    {
        if(t[iter + m] < t[iter + m + 1])
        {
            for(int i = 0; i <= m; i++) for(int k = 0; k <= m; k++) new_coeffs[i][k] = 0.;

            float numerator = pow(t[iter + 1 + m] - t[iter + m], m - 1);
            new_coeffs[m][m] = numerator;
            for(int k = 2; k <= m; k++)
                new_coeffs[m][m] /= t[iter + k + m] - t[iter + m];
            new_coeffs[0][0] = numerator;
            for(int k = 2; k <= m; k++)
                new_coeffs[0][0] /= t[iter + 1 + m] - t[iter + 1 - k + m];
    
            for(int i = 1; i <= m - 1; i++)
                if(m - i - 1 - skip_size >= 0 && m - i - 1 - skip_size <= m)
                    new_coeffs[m - i][m] = old_coeffs[m - i - 1 - skip_size][0];

            for(int i = 1; i <= m - 1; i++)
            {
                v = (t[m + iter - i + 1 + m] - t[iter - i + m])
                    / (t[m - i + iter + 2 + m] - t[-i + iter + 1 + m]);
                float denom = (t[iter + 1 + m] - t[-i + iter + m]);
                c1 = (t[iter + m] - t[-i + iter + m]) / denom;
                c2 = (t[iter + 1 + m] - t[m - i + iter + 2 + m]) / denom;
                c3 = (t[m - i + iter + 2 + m] - t[iter + m]) / denom;
                for(int k = m - 1; k >= 0; k--)
                {
                    new_coeffs[m - i][k] = c1 * new_coeffs[m - i][k + 1] 
                        + v * (c2 * new_coeffs[m - i + 1][k] 
                                + c3 * new_coeffs[m - i + 1][k + 1]);
                }
            }
            if(iter > j)
            {
                for(int i = 0; i <= m; i++) for(int k = 0; k <= m; k++) old_coeffs[i][k] = new_coeffs[i][k];
                for(int i = 0; i <= m; i++) for(int k = 0; k <= m; k++) new_coeffs[i][k] = 0.;
            }
            skip_size = 0;
        }
        else skip_size++;
    }
    for(int k = 0; k <= m; k++) for(int i = 0; i <= m; i++) result[(m + 1) * k + i] = new_coeffs[i][k];

}

void check_digits(int repetitions)
{
    printf("m, n, multi_mean, new_mean\n");
    int ms[7];
    int ns[3];
    ms[0] = 3;
    ms[1] = 4;
    ms[2] = 5;
    ms[3] = 10;
    ms[4] = 20;
    ms[5] = 30;
    ms[6] = 50;
    ns[0] = 10;
    ns[1] = 50;
    ns[2] = 100;
    for(int m_id = 0; m_id < 7; m_id++)
    {
        int m = ms[m_id];
        double result_dBC[(m + 1) * (m + 1)];
        double result_multi[(m + 1) * (m + 1)];
        double result_one[(m + 1) * (m + 1)];
        for(int n_id = 0; n_id < 3; n_id++)
        {
            int n = ns[n_id];
            double mean_digits_multi = 0., mean_digits_one = 0.;
            int knots_max = 2 * m + n + 1;
            double knots[knots_max];
            int total_non_empty_spans = 0;
            for(int r = 0; r < repetitions; r++)
            {
                generate_knots(m, n, knots, -10., 10., 0.5);
                for(int i = knots_max - 2; i >= knots_max - m - 1; i--) knots[i] = knots[knots_max - 1];

                for(int j = 0; j < n; j++)
                {
                    if(knots[m + j] < knots[m + j + 1])
                    {
                        total_non_empty_spans++;
                        coefficients_deboor(m, n, j, knots, result_dBC);
                        coefficients_new(m, n, j, knots, result_one);
                        coefficients_multi(m, n, j, knots, result_multi);
                        for(int res_iter = 0; res_iter < (m + 1) * (m + 1); res_iter++)
                        {
                            double digits_multi = get_digits(result_multi[res_iter],
                                                             result_dBC[res_iter],
                                                             18.);
                            mean_digits_multi += digits_multi;
                            double digits_one = get_digits(result_one[res_iter],
                                                           result_dBC[res_iter],
                                                           18.);
                            mean_digits_one += digits_one;
                        }
                    }
                }
            }
            mean_digits_multi /= total_non_empty_spans * (m + 1) * (m + 1);
            mean_digits_one /= total_non_empty_spans * (m + 1) * (m + 1);
            printf("%d, %d, %1.3f, %1.3f\n", m, n, mean_digits_multi, mean_digits_one);
        }
    }
}


void check_time(int repetitions)
{
    time_t randtime;
    srand((unsigned) time(&randtime));
    clock_t start_t, end_t;
    printf("m, n, new, deBoor\n");
    int ms[7];
    int ns[3];
    ms[0] = 3;
    ms[1] = 4;
    ms[2] = 5;
    ms[3] = 10;
    ms[4] = 20;
    ms[5] = 30;
    ms[6] = 50;
    ns[0] = 10;
    ns[1] = 50;
    ns[2] = 100;
    for(int m_id = 0; m_id < 7; m_id++)
    {
        int m = ms[m_id];
        double result_dBC[(m + 1) * (m + 1)];
        double result_multi[(m + 1) * (m + 1)];
        double result_one[(m + 1) * (m + 1)];
        for(int n_id = 0; n_id < 3; n_id++)
        {
            int n = ns[n_id];
            int knots_max = 2 * m + n + 1;
            double knots[knots_max];
            int total_non_empty_spans = 0;
            double elapsed_dBC = 0.0,
                   elapsed_one = 0.0;
            for(int r = 0; r < repetitions; r++)
            {
                generate_knots(m, n, knots, -10., 10., 0.5);

                start_t = clock();
                for(int j = 0; j < n; j++)
                {
                    if(knots[m + j] < knots[m + j + 1])
                    {
                        coefficients_deboor(m, n, j, knots, result_dBC);
                    }
                }
                end_t = clock();
                elapsed_dBC += (double)(end_t - start_t) / CLOCKS_PER_SEC;

                start_t = clock();
                for(int j = 0; j < n; j++)
                {
                    if(knots[m + j] < knots[m + j + 1])
                    {
                        coefficients_new(m, n, j, knots, result_one);
                    }
                }
                end_t = clock();
                elapsed_one += (double)(end_t - start_t) / CLOCKS_PER_SEC;

            }
            printf("%d, %d, %1.3f, %1.3f\n", m, n, elapsed_one, elapsed_dBC);
        }
    }
}


void toy_case()
{
    printf("====TOY CASE====\n");
    int m = 3;
    int n = 5;
    double knots[12];
    knots[0] = 0.;
    knots[1] = 0.;
    knots[2] = 0.;
    knots[3] = 0.;
    knots[4] = 0.2;
    knots[5] = 0.4;
    knots[6] = 0.4;
    knots[7] = 0.9;
    knots[8] = 1.;
    knots[9] = 1.;
    knots[10] = 1.;
    knots[11] = 1.;
    double result_dBC[(m + 1) * (m + 1)];
    double result_multi[(m + 1) * (m + 1)];
    double result_one[(m + 1) * (m + 1)];
    for(int j = 0; j < n; j++)
    {
        if(knots[m + j] < knots[m + j + 1])
        {
            printf("Evaluating for j = %d\n", j);
            coefficients_deboor(m, n, j, knots, result_dBC);
            coefficients_new(m, n, j, knots, result_one);
            coefficients_multi(m, n, j, knots, result_multi);
            printf("Coefficients for interval [%1.3lf, %1.3lf)\n", knots[m + j], knots[m + j + 1]);
            for(int k = 0; k <= m; k++)
            {
                printf("dBC k = %d: ", k);
                for(int i = 0; i <= m; i++) printf("%1.3lf ", result_dBC[(m + 1) * k + i]);
                printf("\n");
                printf("new k = %d: ", k);
                for(int i = 0; i <= m; i++) printf("%1.3lf ", result_one[(m + 1) * k + i]);
                printf("\n");
                printf("mul k = %d: ", k);
                for(int i = 0; i <= m; i++) printf("%1.3lf ", result_multi[(m + 1) * k + i]);
                printf("\n");
            }
            for(int k = 0; k <= m; k++)
            {
                double sum = 0.;
                for(int i = 0; i <= m; i++) sum += result_dBC[(m + 1) * k + i];
                printf("SUM dBC k = %d: %1.3lf\n", k, sum);
                sum = 0.;
                for(int i = 0; i <= m; i++) sum += result_one[(m + 1) * k + i];
                printf("SUM new k = %d: %1.3lf\n", k, sum);
                sum = 0.;
                for(int i = 0; i <= m; i++) sum += result_multi[(m + 1) * k + i];
                printf("SUM mul k = %d: %1.3lf\n", k, sum);
            }
        }
    }
}

void bezier_case()
{
    printf("====BEZIER CASE====\n");
    int m = 3;
    int n = 1;
    double knots[8];
    knots[0] = 0.;
    knots[1] = 0.;
    knots[2] = 0.;
    knots[3] = 0.;
    knots[4] = 1.;
    knots[5] = 1.;
    knots[6] = 1.;
    knots[7] = 1.;
    double result_dBC[(m + 1) * (m + 1)];
    double result_multi[(m + 1) * (m + 1)];
    double result_one[(m + 1) * (m + 1)];
    for(int j = 0; j < n; j++)
    {
        if(knots[m + j] < knots[m + j + 1])
        {
            coefficients_deboor(m, n, j, knots, result_dBC);
            coefficients_new(m, n, j, knots, result_one);
            coefficients_multi(m, n, j, knots, result_multi);

            printf("Coefficients for interval [%1.3lf, %1.3lf)\n", knots[m + j], knots[m + j + 1]);
            for(int k = 0; k <= m; k++)
            {
                printf("dBC k = %d: ", k);
                for(int i = 0; i <= m; i++) printf("%1.3lf ", result_dBC[(m + 1) * k + i]);
                printf("\n");
                printf("new k = %d: ", k);
                for(int i = 0; i <= m; i++) printf("%1.3lf ", result_one[(m + 1) * k + i]);
                printf("\n");
                printf("mul k = %d: ", k);
                for(int i = 0; i <= m; i++) printf("%1.3lf ", result_multi[(m + 1) * k + i]);
                printf("\n");
            }
        }
    }
}

int main()
{
    // bezier_case();
    // toy_case();
    check_digits(50000);
    check_time(50000);
    return 0;
}
