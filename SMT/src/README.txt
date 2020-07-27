Test instances for points 5 and 6

8x8_general.txt
10x10_general.txt
16x16_general.txt
  

smt_z3_base
- It is the script file that you can use to solve the PWP problem (points 1-4) with SMT using the z3 python library.
- It takes two parameters the path to the folder where the instances are stored and the name of the instance to solve.
- It will produce in output the solution in the required format and automatically generates its plot without the need to 
  call the solution_grid.py script.
- It will save the produced solution in a new folder ("out_base")
Example:
python smt_z3_base.py --instances_path C:\Users\Gayed\Desktop\SMT\src\Instances --file_name 8x8.txt



smt_z3_general
- It is the script file that you can use to solve the PWP problem (points 5,6) with SMT using the z3 python library.
- It takes two parameters the path to the folder where the instances are stored and the name of the instance to solve.
- It will produce in output the solution in the required format and automatically generates its plot without the need to 
  call the solution_grid.py script.
- It will save the produced solution in a new folder ("out_general")
Example:
python smt_z3_general.py --instances_path C:\Users\Gayed\Desktop\SMT\src\Instances --file_name 8x8.txt


smt_LIBv2_base
- It is the script file that you can use to produce the smt encoding, in the LIBv2 syntax, for the points 1-4.
- It takes two parameters the path to the folder where the instances are stored and the name of the instance to solve.
- It will only produce the encoding of the problem in the LIBv2 syntax, then to chek the satisfiablity of the encoding 
  you can simply copy and paste it into the online Z3 Online Demonstrator (https://compsys-tools.ens-lyon.fr/z3/index.php).
  Of course the provided solution will not be in therequired format.
Example:
python smt_LIBv2_base.py --instances_path C:\Users\Gayed\Desktop\SMT\src\Instances --file_name 8x8.txt

smt_LIBv2_general
- It is the script file that you can use to produce the smt encoding, in the LIBv2 syntax, for the points 5,6.
- It takes two parameters the path to the folder where the instances are stored and the name of the instance to solve.
- It will only produce the encoding of the problem in the LIBv2 syntax, then to chek the satisfiablity of the encoding 
  you can simply copy and paste it into the online Z3 Online Demonstrator (https://compsys-tools.ens-lyon.fr/z3/index.php).
  Of course the provided solution will not be in therequired format.
Example:
python smt_LIBv2_base.py --instances_path C:\Users\Gayed\Desktop\SMT\src\Instances --file_name 8x8.txt


Solution Plot
I have also created a script to better visualize the solutions. 
It takes two parameters the path to the folder where the solution is stored and the name of the solution.
Example:
python solution_grid.py --solution_path C:\Users\Gayed\Desktop\SMT\out\base --file_name 8x8-out.txt



