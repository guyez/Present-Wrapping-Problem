Test instances for points 5 and 6

8x8_general.txt
10x10_general.txt
16x16_general.txt

Dzn Converter
You can lunch the script dzn_converter.py to convert the .txt files to .dzn ones.
It takes as parameters the path to the folder where the instances are stored and, a parameter that indicates the "kind" of convertion you want to do (both, base, general).
both: convert all the instances files into dzn files for the base and general case and save them in two separate folders.
base: convert all the instances files into dzn files only for the base case.
general: convert all the instances files into dzn files only for the general case.   
Example: 
python dzn_converter.py --instances_path C:\Users\Gayed\Desktop\CP\src\Instances --target_conversion both

CP_base
It is the Minizinc file for the points 1-4

CP_general
It is the Minizinc file for the points 5,6


Solution Plot
I have also created a script to better visualize the solutions. 
It takes two parameters the path to the folder where the solution is stored and the name of the solution.
Example:
python solution_grid.py --solution_path C:\Users\Gayed\Desktop\CP\out\base --file_name 8x8-out.txt



