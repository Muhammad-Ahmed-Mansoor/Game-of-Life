/*BismIllah Al Rahman Al Raheem
-------------------------------

This program is an implementation of:
		
		John Conway's Game of Life

Presented as Semester Project for CS-114:Fundamentals of Programming by:
	
		1)Muhammad Ahmed Mansoor     Regn#243142
		2)Haziq Arbab				 Regn#247385
		3)Ali Haider Tahir			 Regn#242995
									        			-Class: BEE-10A

About the Game of life
-----------------------
The Game of Life is a cellular-automation, zero-player game, developed by John Conway in 1970.
The original game is played on an infinite grid of cells (one cell is equivalent to one 
character space in our console application). But in our implementation, a finite wrapping 
grid is implemented.
The evolution of cells (dead or alive) is determined by the initial state of the 
grid: the initial state is a called a seed or initial pattern. Each step in the evolution 
is called a generation. Each cell (dead or alive) has exactly 8 neighbors. A cell 
that is dead in the current generation will be alive in the next generation only if 
exactly 3 of its eight neighbors are alive in the current generation. Any live cell 
with more than 3 live neighbors dies in the next generation. Any live cell with fewer 
than 2 live cells in its neighbors dies in the next generation.
This process produces very interesting patterns.
The game of life is a very important mathematical phenomenon, as it can implement
almost all type of computing. For mathematicians, scientists and engineers, it is a 
source of never ending wonder, amusement and learning. To date, thousands of seeds have been
discovered with sizes ranging from 3 cells to many thousands. 

About This Implementation
-------------------------
This program does much more implementing the basic algorithm of the game of life, i.e. the 
decisions of live or dead state of cells. The aim of the program is to make the game of life 
interactive, and enable the user to not only grasp it's fundamental concept, but to develop an
interest in the user to experiment with it.

This program provides the following features:
	
	1)Wrapping Boundaries: 
							This is the first choice the user is presented with, whether
							to turn on boundary wrapping or not. If wrapping is set off, cells at the 
							boundary die automatically. If set on, the boundaries wrap and the grid becomes
							a torus (toroidal array) i.e. the boundary cells are compared with the opposite boundary
							cells.

	2)Pre-Defined Seeds:
							The user can choose between 16 commonly known seeds that have been pre-programmed
							into the game. With the pre-programmed seeds, the user can also select where to 
							place them by specifying the centre. The earlier decision to turn wrapping on 
							or off also comes into play here, as with wrapping off, the "overflowing" seed 
							cells are automatically killed off.

	3)User-Defined seeds: 
							The user may define their own seed by setting cells of their choice alive.
							The user can also save the seed to a txt file.

	4)Load a Seed from Disk:
							The user may load a previously defined and saved seed. User defined seeds
							do not support centre-selection.

	5)Random Seeds:
							The user can opt to let the computer decide how many and which seeds to turn on 
							randomly for some interesting results.

	6)Number of generations:
							The user can choose the number of generations for which the game 
							should run. The limit is between  and INT_MAX as defined in limits.h
							(2147483647 on the PC which was used to code this implementation). Moreover,
							the option to pause and exit the game before the number of generations has
							completed is also available.

	7)Speed:
							The user is given 4 speed controls. Fast, medium and slow respectively correspond to a sleep
							time of 30, 150 and 500 milliseconds between generations. The fourth speed is manual, allowing 
							the user to control when to see the next generation by pressing enter.

	8)Live character of Choice:
							The user can enter any character they wish to view for live cells.
							If the user enters more than one character, only the first is considered.

	9)Still State Detection:
							The game can automatically detect if the grid has become stagnant. This leads to an 
							immediate pause and exit prompt.


Moreover, great care has been taken to make the program as user-friendly as possible.
 

A note on the Program's Portability:
-----------------------------------
The program has been written on Microsoft's visual studio and compiled with Microsoft's Visual C++
compiler which deprecates certain features and replaces them with new ones. These new features are
often not supported by compilers like GCC. Therefore it is recommended that evaluator of the source should
use Visual Studio.

Use of Windows.h makes it quite apparent that this program is written exclusively for Microsoft Windows.
Moreover this program uses the SetConsoleDisplayMode() function from windows.h to make the console open
in fullscreen mode by default. However, because of this, the program can only be used properly on Microsoft's
Windows 10, as previous versions of the windows OS had removed the console fullscreen feature. Thus, unfortunately,
the program is written for only one particular OS. However, this concern was deemed minor by the team as portable
programming practices are neither part of our courseware, nor our evaluation criteria.


A note on the Program's File Handling
-------------------------------------
The feature of saving and loading seeds is based the following files:
	
	1)The Seed Files:		
							The seed files contain an entire copy of the program's grid.
							They are named as seed1.txt, seed2.txt etc.

	2The num_seeds.txt file:
							This file contains one integar, the number of saved seeds.
							This is necessary as it gives the various loops an upper limit.

	3)The seed_record.txt file:
							This file contains the names of the seeds with their respective numbers
							as assigned to the filenames. It allows easy saving and loading of seeds
							without having to employ dynamic memory allocation, taking large string inputs
							from the user, or limiting the number of seeds that may be saved.

The program only checks if num_seeds.txt exists, and enables the seed loading option(otherwise it is 
disabled). The saving function creates a new num_seeds.txt and a new seed_record.txt if it does not 
already exist. 
If num_seeds.txt exists, then the program assumes that the entire system is synchronized, 
i.e. the number in num_seeds.txt is equal to the number of seeds listed in seed_record.txt
which is equal to the number of seedx.txt files. Anything to the contrary is only possible
if the user has interfered with the files. Responsibility for program failure thus lies with the
user in this case.

------------------------------------end




*/




//Libraries used
#include<stdio.h>
#include<time.h>
#include<stdlib.h>
#include<windows.h>
#include<Windows.h>
#include<wincon.h>
#include<limits.h>
#include<string.h>
#include<conio.h>



//function prototypes
void print_current_generation(int spaces, char live);
int cell_state(int i, int j);
void update_current_generation();
void update_previous_generation();
void pre_defined_seed();
void user_defined_seed();
void random_seed();
int validated_input(int min, int max);
void print_header();
void intro_screen();
int compare_generations();
void save_seed();
void load_seed();


/*This program refers to grids using the x-y system as opposed to
the row-col system used in C.
In other words grid[row][col] is written as grid[y][x].
Moreover, the size of the grid has been chosen with much care,
considration and calculation. Evaluator of the source code is therefore requested
not to alter it.*/
#define Y_MAX 40		//Max number of rows
#define X_MAX 70		//Max number of columns

/*The grids are defined as Global Arrays to avoid
having to keep passing them between functions.*/
int previous_generation[Y_MAX][X_MAX] = { { 0 } };
int current_generation[Y_MAX][X_MAX] = { { 0 } };



int wrap,					/*Value of Variable wrap taken from user in main. 1 indicates wrapping is on
							while 0 means off. Made global as it influences code in many functions*/
							seed_files_exist;		//set to 0 or 1 after checking whether any stored seeds exist. Value assigned in main()






void main(void)
{
	//Variable declarations
	int clear_time,				//The time in milliseconds for which screen sleeps before cls. Controls animation speed. -1 means manual animation
		num_generations,		//Number of generations for which the game will run
		generation_count,		//Counter for the main game loop. Runs upto num_generations
		is_still;				//Used in main game loop. Set to 1 if game has become still else 0		


	char live_char[100],		/*A string to store the character to view for a live cell. Only the first character
								live_char[0] is considered but a large string is initialized to account for bad user input */
								user_input[100];		//For user input taken during the game loop

	//These statements allow the console to open in fullscreen mode
	COORD Coord;
	SetConsoleDisplayMode(GetStdHandle(STD_OUTPUT_HANDLE), CONSOLE_FULLSCREEN_MODE, &Coord);

	//Adjusting console colour to white background with black text
	system("color F0");

	intro_screen();

	// Here the various menus with swith-cases start. The code is written to be mostly self documenting
	print_header();
	printf("Do you wish to have wrapping boundaries?\n");
	printf("\t1)Yes.\n");
	printf("\t2)No.\n");
	printf("Enter your choice: ");
	wrap = validated_input(1, 2) % 2;

	//checking if whether any stored seed files exist
	FILE *check_file;
	seed_files_exist = (!fopen_s(&check_file, "num_seeds.txt", "r"));
	if (seed_files_exist)
		fclose(check_file);

	system("cls");
	print_header();
	puts("Would you like to:-");
	puts("\t1)Select from a list of predefined seeds.");
	puts("\t2)Define your own seed.");
	puts("\t3)Let the computer define a random seed.");

	if (seed_files_exist)//option to load a user-saved seed given only if they exist
		puts("\t4)Load a user-saved seed.");

	printf("Select the desired option: ");

	switch (validated_input(1, (seed_files_exist ? 4 : 3)))/*again the conditional operator gives option to
														   load a user-saved seed only if they exist*/
	{
	case 1:
		system("cls");
		pre_defined_seed();
		break;
	case 2:
		system("cls");
		user_defined_seed();
		break;
	case 3:
		system("cls");
		random_seed();
		break;
	case 4:
		system("cls");
		load_seed();
		break;
	default:
		break;

	}//end switch

	print_header();
	printf("Enter the number of generations for which\nyou want to run the game: ");
	num_generations = validated_input(1, INT_MAX);
	system("cls");

	print_header();
	puts("Select the desired speed:-");
	puts("\t1)Fast.");
	puts("\t2)Medium.");
	puts("\t3)Slow.");
	puts("\t4)Manual (You will move to the next generation manually by pressing enter).");
	printf("Select the desired option: ");

	switch (validated_input(1, 4))
	{
	case 1:
		clear_time = 30;
		break;
	case 2:
		clear_time = 150;
		break;
	case 3:
		clear_time = 500;
		break;
	case 4:
		clear_time = -1;
		break;
	default:
		break;

	}//end switch


	system("cls");
	print_header();


	printf("Enter a charachter for living cells: ");

	do//This do-while loop is to ensure that an empty character is not entered because it may crash the game
	{
		fflush(stdin);
		gets_s(live_char, 100);
		fflush(stdin);
	} while (!strlen(live_char));



	/*These statements set the output to print screen by screen instead of line by line
	All output is sent to char array buffer and sent to screen only when fflush(stdout) is called.
	This technique prevents the flicker caused by normal line-by-line output.*/
	char buffer[Y_MAX*X_MAX + 100];
	setvbuf(stdout, buffer, _IOFBF, sizeof(buffer));


	update_previous_generation();//So the seed is also copied to previous_generation array

	//Main game loop begins.
	for (generation_count = 1; generation_count <= num_generations; generation_count++)
	{
		system("cls");
		printf("Generation#%d:-\n\n", generation_count);//display generation counter
		print_current_generation(10, live_char[0]);
		fflush(stdout);


		update_current_generation();
		is_still = compare_generations();
		update_previous_generation();

		if (generation_count == num_generations)//checks if last generation reached
		{
			puts("\n\nFinal generation reached.");
			break;

		}//end if

		else if (generation_count == 1)//to pause the game at first generation so user can view seed
		{
			printf("\n\nThis is the seed.\nPress enter to start animation.");
			fflush(stdout);
			fflush(stdin);
			getchar();
			fflush(stdin);
		}//end else if

		else if (is_still)//End the game if it has become still
		{
			puts("\n\nThe Game has reached a still state.");
			break;
		}//end else if

		else if (clear_time == -1)//If speed is set to manual, this code is executed
		{
			fflush(stdin);//if user types in string of lenthh n, n cycles get skipped. Flushing stops that rogue phenomenon
			puts("\n\nPress enter to display next generation.");
			puts("To quit, type 0 and then press enter.");
			fflush(stdout);
			if (getchar() == '0')//exit if user enters 0
				break;

		}//end else if

		else//For normal and non-manual-speed situations, the loop repeats after an instantaneous pause
		{
			puts("\n\nPress any key to pause.");
			fflush(stdout);
			if (_kbhit())//if keyboard hit detected, pause the game
			{
				fflush(stdout);
				fflush(stdin);
				puts("\nPress enter to continue. To quit, type 0 and press enter.");//on pausing, entering 0 allows user to exit
				fflush(stdout);
				fflush(stdin);
				if (getchar() == '0')
					break;
				fflush(stdin);
			}

			Sleep(clear_time);
		}//end else 

	}//end for



	//Final message
	puts("Thank you for playing The Game of Life\nPress enter to exit.");
	fflush(stdout);
	fflush(stdin);
	getchar();
	fflush(stdin);
}//end main

//--------------------------------------------------------------------------------------------------------------------------------

/*Prints the current_generation with a boundary and x-y labels.

	int spaces: The horizontal indentation of the entire grid.
	char live: The character to be used for live cells*/
void print_current_generation(int spaces, char live)
{
	

	//printing spaces
	for (int i = 1; i <= spaces; i++)
	{
		printf(" ");
	}//end for


	//printing the tens for the x-labels
	for (int j = 0; j < X_MAX; j++)
	{
		if (j % 10 == 0 && j != 0)
		{
			printf("%2d", j / 10);
		}//end if
		else
		{
			printf("  ");
		}//end else

	}//end for


	//printing spaces
	puts("");
	for (int i = 1; i <= spaces; i++)
	{
		printf(" ");
	}//end for


	//printing the units for the x-labels
	for (int j = 0; j < X_MAX; j++)
	{
		printf("%2d", j % 10);

	}//end for

	//printing spaces
	puts("");
	for (int i = 1; i <= spaces; i++)
	{
		printf(" ");
	}//end for


	//printing upper boundary
	for (int j = 0; j <= X_MAX; j++)
	{
		(printf("--"));

	}//end for

	//printing the grid with the side boundaries
	puts("");
	for (int i = 0; i < Y_MAX; i++)
	{
		//printing spaces
		for (int a = 1; a <= spaces - 2; a++)
		{
			printf(" ");
		}//end inner for


		//printing the y-label, and left boundary pipe(|)
		printf("%2d|", (i % 10 == 0) ? i : i % 10);


		//printing the ith row
		for (int j = 0; j < X_MAX; j++)
		{
			(current_generation[i][j] == 0) ? (printf("  ")) : printf("%c ", live);

		}//end inner for

		puts("|");//left boundary pipe

	}//end outer for


	//printing spaces
	for (int i = 1; i <= spaces; i++)
	{
		printf(" ");
	}//end for

	//printing lower boundary
	for (int j = 0; j <= X_MAX; j++)
	{
		(printf("--"));

	}//end for


	return;
}//end function print_current_generation()
//---------------------------------------------------------------------------------------------------------------------------------


/*Decides if the cell at position y=i and x=j should be set alive(1) or dead(0)
	int i: y coordinate of the cell to be checked
	int j: x coordinate of the cell*/
int cell_state(int i, int j)
{
	

	int y_neighbour, x_neighbour;//store the coordinates of the neighbour under consideration

	//If wrapping is off then boundary cells automatically die
	if ((i == 0 || i == Y_MAX - 1 || j == 0 || j == X_MAX - 1) && (!wrap))
	{
		return 0;
	}


	int living_neighbours_count = 0;//the number of live neighbours of the i-j cell

	for (int y_count = -1; y_count <= 1; y_count++)//iterates through the three rows i-1, i, i+1
	{

		for (int x_count = -1; x_count <= 1; x_count++)//iterates through the three columns j-1, j, j+1
		{
			if (y_count == 0 && x_count == 0)
				continue;//the cell i-j is not a neighbour so is not processed

			y_neighbour = i + y_count;
			x_neighbour = j + x_count;

			if (wrap)
			{
				//This code enables the wrapping boundaries

				//for the top row, the upper neighbours are set as the bottom row
				if (y_neighbour == -1)
					y_neighbour = Y_MAX - 1;

				//for the bottom row, the lower neighbours are set as the upper row
				if (y_neighbour == Y_MAX)
					y_neighbour = 0;

				//for the leftmost column, the left neighbours are set as the rightmost column
				if (x_neighbour == -1)
					x_neighbour = X_MAX - 1;

				//for the rightmost column, the right neighbours are set as the leftmost column
				if (x_neighbour == X_MAX)
					x_neighbour = 0;
			}//end if


			//increment neighbour counter if neighbour was alive in prevoius_generation
			if (previous_generation[y_neighbour][x_neighbour] == 1)
			{
				living_neighbours_count++;
			}//end if

		}// end inner for
	}//end outer for

	//for a cell alive in previous_generation, it remains alive if it has 2 or 3 alive neighbours
	if ((previous_generation[i][j] == 1) && (living_neighbours_count == 2 || living_neighbours_count == 3))
	{
		return 1;
	}//end if

	//for a cell dead in previous_generation, it becomes alive if it exactly 3 alive neighbours
	else if ((previous_generation[i][j] == 0) && (living_neighbours_count == 3))
	{
		return 1;
	}//end else if

	//for all other cases, the cell is dead
	else
	{
		return 0;
	}//end else

}//end function cell_state()
//-------------------------------------------------------------------------------------------------------------------------------

/*Uses the cell state function and iterates through the entire current_generation
to update all cells*/
void update_current_generation()
{	
	for (int y_count = 0; y_count <Y_MAX; y_count++)
	{
		for (int x_count = 0; x_count <X_MAX; x_count++)
		{
			current_generation[y_count][x_count] = cell_state(y_count, x_count);//cell (x_count,y_count) is set 0 or 1 as decided by cell_state()

		}// end inner for
	}// end outer for

	return;
}//end function update_current_generation()
//----------------------------------------------------------------------------------------------------------------------------------


/*Simply copies current_generation onto
previous_generation*/
void update_previous_generation()
{
	

	for (int y_count = 0; y_count <Y_MAX; y_count++)
	{
		for (int x_count = 0; x_count <X_MAX; x_count++)
		{
			previous_generation[y_count][x_count] = current_generation[y_count][x_count];

		}// end inner for
	}// end outer for

	return;
}//end function update_previous_generation()
//----------------------------------------------------------------------------------------------------------------------------------


/*In this function, some common seeds are pre-defined. This function asks the user for the desired seed and plants
it in the current_generation*/
void pre_defined_seed()
{
	


	int *x=NULL, *y=NULL,		 //will be set to point to the x and y arrays of the seed selected by user
		y_coord, x_coord,		 //the cells at these coordinates will be set alive
		x_origin, y_origin,		 //the centre of the seed as chosen by the user	
		num_cells;				 //num of live cells in the selected seed


	//seed selection menu
	print_header();
	puts("Select one of the following seeds:-");
	puts("\n\t SEEDS                                                   DESCRIPTIONS");
	puts("\t _____                                                   ____________");
	puts("\n\t                           OSCILLATORS");
	puts("\t                           -----------\n");
	puts("\t 1)Tumbler.                                                An elegant oscillator with a period of 14 generations.");
	puts("\t 2)Blinker.                                                A very simple oscillator consisting of 3 cells having a period of 2 generations.");
	puts("\t 3)Toad.                                                   A relatively uninteresting period 2 oscillator.");
	puts("\t 4)Beacon.                                                 A period 2 oscillator consisting of two diagonally touching blocks.");
	puts("\t 5)Exploder/Pulsar.                                        A large, visually stunning period 3 oscillator, having four symmetric quadrants.");
	puts("\t 6)Small Exploder.                                         Initially looks somewhat like the exploder but eventually becomes a still life. Technically not an oscillator.");
	puts("\t 7)10 Cell Row.                                            A brilliant example that a book should not be judged by it's cover.");
	puts("\t 8)11 Cell Row.                                            Becomes two blinkers after 15 generations.");
	puts("\n\t                      GLIDERS AND SPACESHIPS");
	puts("\t                      ----------------------\n");
	puts("\t 9)Light Weight Spaceship(Horizontal).                     A simple spaceship moving horizontally.");
	puts("\t10)Light Weight Spaceship(Vertical).                       A simple spaceship moving vertically.");
	puts("\t11)Glider.                                                 Consider it a tiny, diagonally moving, less interesting spaceship");
	puts("\t12)Gosper Glider Gun.                                      A giant glider-producing machine. Produces its first glider on 15th generation, then one after every 30.");
	puts("\n\t                       STILL LIFE PATTERNS");
	puts("\t                       -------------------\n");
	puts("\t13)Block.                                                  The most boring of the still patterns; a difficult title to earn.");
	puts("\t14)Boat.                                                   Looks like a boat being viewed from above; a boat that can't swim.");
	puts("\t15)Loaf.                                                   No, it does not look like a loaf of bread.");
	puts("\t16)Beehive.                                                If all beehives were this calm.\n");


	printf("Select the desired option: ");

	/*Based on the user's selection, two arrays a and b are defined. a contains the y-coordinates (row#)
	of the cells to be set alive while b contains the x-coordinates(col#). Their pointers are copied to x and y
	because the scope of identifiers a and b exists only in this switch block.
	Also, the numbers in the arrays are not the actual coordinates. Rather they are the coordinates
	relative to the centre (x_origin,y_origin) to be specified later by the user. For example, an entry 4 in an "a" array with
	corresponding entry -1 in "b" array means that the cell at current_generation[y_origin+4][x_origin-1] will be set to 1.*/

	switch (validated_input(1, 16))
	{
	case 1://tumbler
		num_cells = 22;
		int a1[] = { -2, -1, 0, 1, 2, -2, -1, 0, 1, 2, -2, -1, 3, -2, -1, 3, 1, 2, 3, 1, 2, 3 };
		int b1[] = { -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, -2, -2, -2, 2, 2, 2, -3, -3, -3, 3, 3, 3 };
		y = a1;
		x = b1;

		break;
	case 2://blinker
		num_cells = 3;
		int a2[] = { 0, 0, 0 };
		int b2[] = { -1, 0, 1 };
		y = a2;
		x = b2;

		break;
	case 3://toad
		num_cells = 6;
		int a3[] = { 0, 1, 0, 1, 1, 0 };
		int b3[] = { 0, 0, 1, 1, -1, 2 };
		y = a3;
		x = b3;

		break;
	case 4://beacon
		num_cells = 6;
		int a4[] = { -1, 0, -1, 2, 1, 2 };
		int b4[] = { 0, -1, -1, 1, 2, 2 };
		y = a4;
		x = b4;

		break;
	case 5://Exploder/Pulsar
		num_cells = 12;
		int a5[] = { -2, 2, -2, -1, 0, 1, 2, -2, -1, 0, 1, 2 };
		int b5[] = { 0, 0, -2, -2, -2, -2, -2, 2, 2, 2, 2, 2 };

		//Below is our first attempt at the pulsar. It took so much work that we didn't have the heart to remove it 
		//int a[] = { -4, -3, -2, 2, 3, 4, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -4, -3, -2, 2, 3, 4, -6, -6, -6, -6, -6, -6, 6, 6, 6, 6, 6, 6, -4, -3, -2, 2, 3, 4, -4, -3, -2, 2, 3, 4 };
		//int b[] = { -1, -1, -1, -1, -1, -1, -4, -3, -2, 2, 3, 4, -4, -3, -2, 2, 3, 4, 1, 1, 1, 1, 1, 1, -4, -3, -2, 2, 3, 4, -4, -3, -2, 2, 3, 4, -6, -6, -6, -6, -6, -6, 6, 6, 6, 6, 6, 6 };

		y = a5;
		x = b5;

		break;
	case 6://Small Exploder
		num_cells = 7;
		int a6[] = { 0, 0, -1, -1, -1, -2, 1 };
		int b6[] = { -1, 1, -1, 0, 1, 0, 0 };
		y = a6;
		x = b6;

		break;
	case 7://10 Cell Row
		num_cells = 10;
		int a7[] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
		int b7[] = { -5, -4, -3, -2, -1, 0, 1, 2, 3, 4 };
		y = a7;
		x = b7;

		break;
	case 8://11 cell row
		num_cells = 11;
		int a8[] = { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
		int b8[] = { -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5 };
		y = a8;
		x = b8;

		break;
	case 9://Light Weight Spaceship(Horizontal).
		num_cells = 9;
		int a9[] = { -1, -1, -1, -1, 0, 0, 1, 2, 2 };
		int b9[] = { -1, 0, 1, 2, -2, 2, 2, -2, 1 };
		y = a9;
		x = b9;

		break;
	case 10://Light Weight Spaceship(Vertical)
		num_cells = 9;
		int b10[] = { -1, -1, -1, -1, 0, 0, 1, 2, 2 };
		int a10[] = { -1, 0, 1, 2, -2, 2, 2, -2, 1 };
		y = a10;
		x = b10;

		break;
	case 11://Glider
		num_cells = 5;
		int a11[] = { 0, 1, -1, 0, 1 };
		int b11[] = { -1, 0, 1, 1, 1 };
		y = a11;
		x = b11;

		break;
	case 12://Gosper Glider Gun
		num_cells = 35;
		int a12[] = { 0, -1, -1, 0, 1, -3, -4, -3, -5, -4, -5, 7, 8, 7, 9, 7, -2, -3, -3, -1, -1, -2, -2, -3, -2, -3, -4, -5, -4, -5, 2, 3, 4, 2, 3 };
		int b12[] = { -1, -2, -3, -3, -3, 3, 3, 4, 4, 5, 5, 5, 5, 6, 6, 7, -9, -9, -10, -10, -11, -11, -18, -18, -19, -19, 15, 15, 16, 16, 16, 16, 16, 17, 18 };
		y = a12;
		x = b12;


		break;
	case 13://Block
		num_cells = 4;
		int a13[] = { 0, 0, 1, 1 };
		int b13[] = { 0, 1, 0, 1 };
		y = a13;
		x = b13;

		break;
	case 14://Boat
		num_cells = 5;
		int a14[] = { -1, 0, -1, 1, 0 };
		int b14[] = { -1, -1, 0, 0, 1 };
		y = a14;
		x = b14;

		break;
	case 15://Loaf
		num_cells = 7;
		int a15[] = { 0, -1, 1, -1, 2, 0, 1 };
		int b15[] = { -2, -1, -1, 0, 0, 1, 1 };
		y = a15;
		x = b15;

		break;
	case 16://Beehive
		num_cells = 6;
		int a16[] = { 0, 0, -1, -1, 1, 1 };
		int b16[] = { -1, 2, 0, 1, 0, 1 };
		y = a16;
		x = b16;

		break;
	default:
		break;


	}//end switch

	//Asking user for the centre of the seed to be planted
	system("cls");
	print_current_generation(10, '*');
	printf("\n\nPlease choose the location of the centre of the seed in the above %d by %d grid.\n", Y_MAX, X_MAX);
	printf("Remember, for best results the centre (%d,%d) is recommended.\n", X_MAX / 2, Y_MAX / 2);
	printf("Enter x-coordinate: ");
	x_origin = validated_input(0, X_MAX - 1);
	printf("Enter y-coordinate: ");
	y_origin = validated_input(0, Y_MAX - 1);


	/*this for-loop applies the seed onto current_generation by simply
	iterating through the arrays x and y and setting the cell at location (x,y) to 1*/
	for (int c = 0; c < num_cells; c++)
	{
		x_coord = x[c] + x_origin;
		y_coord = y[c] + y_origin;

		//A similar wrapping mechanism as before
		if (wrap)
		{
			if (y_coord <0)
				y_coord = Y_MAX + y_coord;
			if (y_coord > Y_MAX - 1)
				y_coord = y_coord - Y_MAX;
			if (x_coord <0)
				x_coord = X_MAX + x_coord;
			if (x_coord >X_MAX - 1)
				x_coord = x_coord - X_MAX;
		}//end if

		//if wrapping is off, then all the "overflowing" seed cells shall be ignored and not planted
		else if (y_coord<0 || x_coord <0 || x_coord >X_MAX - 1 || y_coord > Y_MAX - 1)
		{
			continue;
		}//end else if

		current_generation[y_coord][x_coord] = 1;
	}//end for

	system("cls");
	return;

}//end function pre_defined_seeds()
//----------------------------------------------------------------------------------------------------------------------------------


/*This function allows the user to define their own seed by setting
cells of their choice alive*/
void user_defined_seed()
{
	

	int y, x,			//coordinates of the cell to set live
		count = 1;		//a counter for the number of seeds that have been set alive


	while (count<Y_MAX*X_MAX)       //Y_MAX * XMAX is the total number of cells in the grid
	{
		print_current_generation(10, '*');//display the grid with live results as the user inputs!

		//taking user input for x-coordinate
		printf("\n\n\t>>For cell#%d:-\n", count);
		printf("Enter x-coordinate (0-%d or -1 to end seeding): ", X_MAX - 1);
		x = validated_input(-1, X_MAX - 1);

		//for termination of seeding process and choice of saving
		if (x == -1)
		{
			puts("\nSeeding process terminated successfully.");
			printf("You set %d cells alive.\n", count - 1);

			printf("Do you wish to save this seed?\n");
			printf("\t1)Yes.\t");
			printf("\t2)No.\n");
			printf("Enter your choice: ");
			if (validated_input(1, 2) % 2)
			{
				system("cls");
				save_seed();
				return;

			}

			system("pause");
			system("cls");
			return;

		}//end if

		//taking user input for y-coordinate
		printf("Enter y-coordinate (0-%d): ", Y_MAX - 1);
		y = validated_input(0, Y_MAX - 1);

		//If the selected cell is already alive, prompt user for re-entry
		if (current_generation[y][x] == 1)
		{
			puts("This cell is already alive.");
			puts("Press enter to try again.");
			fflush(stdin);
			getchar();
			fflush(stdin);

		}//end if

		//Else set the given cell alive and increment count
		else
		{
			current_generation[y][x] = 1;
			count++;
		}//end else

		system("cls");
	}//end while

	//The user is not expected to ever see this prompt. But then again, some people have too much time on their hands
	puts("Seeding limit reached.");
	printf("You set %d cells alive.\n", count - 1);
	system("pause");
	system("cls");
	return;


}//end function user_defined_seed()
//----------------------------------------------------------------------------------------------------------------------------------


/*Generates a random seed. Both the number of cells to be set live and their
locations are random. The function is pretty much self-explaining*/
void random_seed()
{
	

	srand(time(NULL));
	int num_cells, y, x;

	num_cells = 1 + rand() % ((Y_MAX*X_MAX) - 1);

	for (int count = 1; count <= num_cells; count++)
	{
		y = rand() % Y_MAX;
		x = rand() % X_MAX;
		current_generation[y][x] = 1;
	}//end for

	return;
}//end function random_seed()
//----------------------------------------------------------------------------------------------------------------------------------

/*This function take user input and ensures it is between min and max inclusive.
If not, or if it is garbage input, it prompts user again and again. Once input in the desired
range is obtained, it is returned.*/
int validated_input(int min, int max)
{
	

	int user_selection;
	scanf_s("%d", &user_selection);

	while (user_selection > max || user_selection < min)
	{
		fflush(stdin);
		puts("Invalid Input.");
		printf("Please enter a number in the range %d-%d : ", min, max);
		scanf_s("%d", &user_selection);

	}//end while

	return user_selection;

}//end function validated_input()
//----------------------------------------------------------------------------------------------------------------------------------

//prints a simple header for empty-looking menu screens
void print_header()
{
	
	puts("");
	printf("     J O H N     C O N W A Y' S    0 0 0 0 0         0 0 0    0 0 0 0 0      0         0 0 0 0 0   0 0 0 0 0   0 0 0 0 0    \n");
	printf("     0 0 0 0    0 0 0     0   0    0                0     0   0              0             0       0           0            \n");
	printf("   0           0     0   0 0 0 0   0 0 0 0          0     0   0 0 0 0        0             0       0 0 0 0     0 0 0 0      \n");
	printf("   0   0 0 0   0 0 0 0   0  0  0   0                0     0   0              0             0       0           0            \n");
	printf("     0 0 0     0     0   0     0   0 0 0 0 0         0 0 0    0              0 0 0 0   0 0 0 0 0   0           0 0 0 0 0    \n");
	puts("\n\n\n\n");
	return;
}//end function print_header()
//----------------------------------------------------------------------------------------------------------------------------------


//Prints the intro screen
void intro_screen()
{
	
	puts("");
	printf("                                     ______  ____         __         ____  ____   __               _____           |  ______                         \n");
	printf("                                        |   |    | |   | |  |  |    |     |    | |  |  | |      | |     | |     |    |                               \n");
	printf("                                        |   |    | |---| |  |  |    |     |    | |  |  | |  __  | |-----| |_____|    |-----|                         \n");
	printf("                                      __/   |____| |   | |  |__|    |____ |____| |  |__| |_|  |_| |     |    |       ______|                         \n");
	printf("                                                                                                             |                                        \n");
	printf("                                                                                                                                                     \n");
	printf("                                                                                                                                                     \n");
	printf("                                                                                                                                                     \n");
	printf("                           ____________    ________    _____________    _________                                                                    \n");
	printf("                          |  __________|  |  _____ |  |  ___   ___  |  |  _______|                                                                   \n");
	printf("                          | |             | |    | |  | |   | |   | |  | |                                                                           \n");
	printf("                          | |    ______   | |    | |  | |   |_|   | |  | |-----|                                                                     \n");
	printf("                          | |   |____  |  | |____| |  | |         | |  | |-----|                                                                     \n");
	printf("                          | |________| |  | |    | |  | |         | |  | |_______                                                                    \n");
	printf("                          |____________|  |_|    |_|  |_|         |_|  |_________|                                                                   \n");
	printf("                                                                                                                                                     \n");
	printf("                                                                          __________    _________                                                    \n");
	printf("                                                                         |  ______  |  |  _______|                                                   \n");
	printf("                                                                         | |      | |  | |                                                           \n");
	printf("                                                                         | |      | |  | |______                                                     \n");
	printf("                                                                         | |      | |  |  ______|                                                    \n");
	printf("                                                                         | |______| |  | |                                                           \n");
	printf("                                                                         |__________|  |_|                                                           \n");
	printf("                                                                                                                                                     \n");
	printf("                                                                                         _            _    _________    _________                    \n");
	printf("                                                                                        | |          | |  |  _______|  |  _______|                   \n");
	printf("                                                                                        | |          | |  | |          | |                           \n");
	printf("                                                                                        | |          | |  | |______    | |-----|                     \n");
	printf("                                                                                        | |          | |  | |______|   | |-----|                     \n");
	printf("                                                                                        | |_______   | |  | |          | |_______                    \n");
	printf("     __  __   __  __   __  _    ___  __  ___    __                                      |_________|  |_|  |_|          |_________|                   \n");
	printf("    |__||__| |__ |__  |__ | | |  |  |__ |   |  |__| |__| 0                                                                                           \n");
	printf("    |   | \\  |__  __| |__ | |_|  |  |__ |__/   |__/   |  0                                                                                          \n");
	printf("           __        _ _   __   __    _ _   __   _     __   __   __   __                                                                             \n");
	printf("      --> |__| |__| | | | |__| |  |  | | | |__| | | | |__  |  | |  | |__|                                                                            \n");
	printf("          |  | |  | |   | |  | |__/  |   | |  | | |_|  __| |__| |__| | \\                                                                            \n");
	printf("           __      ___        __  ___  __   __  __                                                                                                   \n");
	printf("      --> |__| |    |   |__| |__|  |  |  | |__ |__|                                                                                                  \n");
	printf("          |  | |__ _|_  |  | |  | _|_ |__/ |__ | \\                                                                                                  \n");
	printf("                __   ___ ___  __    __  __   __   __   __                                                                                            \n");
	printf("      --> |__| |__|   /   |  |  |  |__||__| |__| |__| |__|                                                                                           \n");
	printf("          |  | |  |  /__ _|_ |_\\|  |  || \\  |__/ |  | |__/                                                                                         \n");
	printf("                                                                                                                                                     \n");
	puts("");
	puts("");
	puts("");
	puts("");

	system("pause");
	system("cls");
}//end function intro_screen()
//----------------------------------------------------------------------------------------------------------------------------------

/*Simply compares current_generation and previous_generations.
Returns 1 if equal else 0*/
int compare_generations()
{
	
	for (int i = 0; i < Y_MAX; i++)
	{
		for (int j = 0; j < X_MAX; j++)
		{
			if (current_generation[i][j] != previous_generation[i][j])
			{
				return 0;//the two generaions are not same
			}//end if

		}//end inner for

	}//end outer for


	return 1;//the two generations are same
}//end function compare_generations()
//----------------------------------------------------------------------------------------------------------------------------------

/*This function displays the user saved seeds, allows
the user to pick one, then loads the choice and copies it
to current_generation*/
void load_seed()
{
	

	//variable initializations
	int num_seeds,				//number of stored seeds as read from num_seeds.txt
		current_seed_num,		//the current seed# read from seed_record.txt 
		selected_seed_num,		//the seed# selected by the user
		y_count, x_count,		//counters for the seed-copy loop
		current_cell;			//the current cell read from the selected seed file

	FILE *file_num_seeds,		//num_seeds.txt
		*file_selected_seed,		//the selected seed file 
		*file_seed_record;		//seed_record.txt

	char current_seed_name[100],					//the current seed name read from seed_record.txt 
		selected_seed_file_name[10];		//the selected seed file name

	//opening num_states.txt and seed_record.txt for reading
	fopen_s(&file_num_seeds, "num_seeds.txt", "r");
	fopen_s(&file_seed_record, "seed_record.txt", "r");

	fscanf_s(file_num_seeds, "%d", &num_seeds);

	//now printing menu
	print_header();
	puts("Following saved seeds have been found:\n");
	for (int a = 1; a <= num_seeds; a++)
	{
		//reading seed# and seed name from seed_record.txt
		fscanf_s(file_seed_record, "%d", &current_seed_num);
		fgets(current_seed_name, 100, file_seed_record);

		//printing them on the screen
		printf("\t%d)%s", current_seed_num, current_seed_name);

	}//end for

	//taking user input
	printf("\n\nSelect the desired option:");
	selected_seed_num = validated_input(1, num_seeds);

	//putting the selected_seed_num into the filename
	sprintf_s(selected_seed_file_name, 10, "seed%d.txt", selected_seed_num);

	//closing previously opened files
	fclose(file_num_seeds);
	fclose(file_seed_record);

	//opening the file containing desired seed. 
	fopen_s(&file_selected_seed, selected_seed_file_name, "r");

	//reading seed from file and copying to current_generation
	for (y_count = 0; y_count < Y_MAX; y_count++)
	{
		for (x_count = 0; x_count < X_MAX; x_count++)
		{

			fscanf_s(file_selected_seed, "%d", &current_cell);
			current_generation[y_count][x_count] = current_cell;

		}//end inner for
	}//end outer for

	fclose(file_selected_seed);
	puts("\nLoad Successful.");
	system("pause");
	system("cls");
	return;
}//end function load_seed()
//----------------------------------------------------------------------------------------------------------------------------------

/*This function saves a user-defined seed onto the disk as a
txt file. The number of seeds is incremented in num_seeds.txt and the number and
name of new seed is updated in seed_record.txt. The new file is saved as
seedx.txt where x is the number assigned to it.*/
void save_seed()
{
	

	FILE *file_num_seeds = NULL,		//num_seeds.txt 
		*file_seed_record = NULL,		//seed_record.txt
		*file_new_seed = NULL;			//seedx.txt

	int num_seeds = 0;				//number of seeds as read from num_seeds.txt

	char new_file_name[100],		//name of the new file
		new_seed_name[100];		//name of the new seed given by the user


	//if num_seeds file exists, it is simply read from and opened. seeds_record is opened for appending
	if (seed_files_exist)
	{
		fopen_s(&file_num_seeds, "num_seeds.txt", "r");
		fscanf_s(file_num_seeds, "%d", &num_seeds);
		fclose(file_num_seeds);
		file_num_seeds = NULL;
	}//end if


	//taking seed name from user
	print_header();
	printf("Please Enter a name for your Seed:");

	do//This do-while loop is to ensure that an empty character is not entered because it may crash the game
	{
		fflush(stdin);
		gets_s(new_seed_name, 100);
	} while (!strlen(new_seed_name));

	//updating seed_record.txt and num_seed.txt
	fopen_s(&file_seed_record, "seed_record.txt", "a");
	fopen_s(&file_num_seeds, "num_seeds.txt", "w");
	num_seeds++;
	fprintf(file_num_seeds, "%d", num_seeds);
	fprintf(file_seed_record, "%d %s\n", num_seeds, new_seed_name);
	fclose(file_num_seeds);
	fclose(file_seed_record);

	//creating and opening file for new seed
	sprintf_s(new_file_name, 100, "seed%d.txt", num_seeds);
	fopen_s(&file_new_seed, new_file_name, "w");

	//writing new seed onto file
	for (int i = 0; i < Y_MAX; i++)
	{
		for (int j = 0; j < X_MAX; j++)
		{
			fprintf(file_new_seed, "%d ", current_generation[i][j]);
		}//end inner for
		fprintf(file_new_seed, "\n");
	}//end outer for


	fclose(file_new_seed);

	puts("\nSave Successful.");
	system("pause");
	system("cls");
	return;
}//end function save_seed()
//----------------------------------------------------------------------------------------------------------------------------------