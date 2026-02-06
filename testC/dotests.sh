gcc -I. unity.c ../libC/*.c test_helpers.c test_cases.c test_main.c -o test_runner -lgc
./test_runner