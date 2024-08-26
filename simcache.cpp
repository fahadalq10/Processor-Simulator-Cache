/*
CS-UY 2214
Adapted from Jeff Epstein
Starter code for E20 cache Simulator
simcache.cpp
*/

#include <cstddef>
#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <limits>
#include <iomanip>
#include <regex>

using namespace std;


// Some helpful constant values that we'll be using.
size_t const static NUM_REGS = 8;
size_t const static MEM_SIZE = 1<<13;
size_t const static REG_SIZE = 1<<16;
size_t pc = 0;

//REGISTERS

vector<uint16_t> registers(8,0); //{0,0,0,0,0,0,0,0} init 0
void print_log_entry(const string &cache_name, const string &status, int pc, int addr, int row) {
    cout << left << setw(8) << cache_name + " " + status <<  right <<
         " pc:" << setw(5) << pc <<
         "\taddr:" << setw(5) << addr <<
         "\trow:" << setw(4) << row << endl;
}
void load_machine_code(ifstream &f, uint16_t mem[]) {
    regex machine_code_re("^ram\\[(\\d+)\\] = 16'b(\\d+);.*$");
    size_t expectedaddr = 0;
    string line;
    while (getline(f, line)) {
        smatch sm;
        if (!regex_match(line, sm, machine_code_re)) {
            cerr << "Can't parse line: " << line << endl;
            exit(1);
        }
        size_t addr = stoi(sm[1], nullptr, 10);
        unsigned instr = stoi(sm[2], nullptr, 2);
        if (addr != expectedaddr) {
            cerr << "Memory addresses encountered out of sequence: " << addr << endl;
            exit(1);
        }
        if (addr >= MEM_SIZE) {
            cerr << "Program too big for memory" << endl;
            exit(1);
        }
        expectedaddr ++;
        mem[addr] = instr;
    }
}
// Block class that consists of the valid bits, tag, and LRU
class Block {
private:
    bool valid;
    int tag;
    int LRU;

public:
    // Default constructor
    Block() : valid(false), tag(-1), LRU(0) {}

    // Constructor with initialization list
    Block(bool val, int tag, int lru): valid(val), tag(tag), LRU(lru) {}

    // Getters and setters
    bool getValid() const { return valid; }
    int getTag() const { return tag; }
    int getLRU() const { return LRU; }
    void setValid(bool newval) { valid = newval; }
    void setTag(int newtag) { tag = newtag; }
    void setLRU(int newLRU) { LRU = newLRU; }
};

// Cache class that manages cache blocks
class Cache {
private:
    string name;
    int size;
    int assoc;
    int blocksize;
    int rows;
    vector<vector<Block>> cacheBlock;

public:
    // Constructor with initialization list
    Cache(const string& Cname, int size, int assoc, int blocksize, int row)
    : name(Cname), size(size), assoc(assoc), blocksize(blocksize), rows(row) {
        cacheBlock.resize(row);  // Adjust size to desired cache row and block sizes
        for (size_t i = 0; i < row; i++) {
            cacheBlock[i].resize(assoc);
        }
    }

    // Default constructor
    Cache(const string& Cname): name(Cname), size(-1), assoc(-1), blocksize(-1), rows(rows) {}

    // Updates LRU value for cache blocks in a row
    void updateLRU(int row, int ind) {
        for (size_t i = 0; i < cacheBlock[row].size(); ++i) {
            if (cacheBlock[row][i].getLRU() <= cacheBlock[row][ind].getLRU()) {
                cacheBlock[row][i].setLRU(cacheBlock[row][i].getLRU() + 1);
            }
        }
        cacheBlock[row][ind].setLRU(0);
    }

    // Cache access function that handles hits, misses, and evictions
    bool cacheaccess(uint16_t address, size_t pc, bool sw) {
        int blockID = address / blocksize;
        int row = blockID % rows;
        int tag = blockID / rows;
        size_t final = 0;

        if (sw == true) {  // For SW calls
            for (size_t i = 0; i < assoc; ++i) {
                if (cacheBlock[row][i].getValid())
                    if (cacheBlock[row][i].getTag() == tag) {
                        updateLRU(row, i);
                        print_log_entry(name, "SW", pc, address, row);
                        return true;
                    }
            }
            // Miss
            for (size_t i = 0; i < assoc; ++i) {
                if (!cacheBlock[row][i].getValid()) {
                    cacheBlock[row][i].setValid(true);
                    cacheBlock[row][i].setTag(tag);
                    cacheBlock[row][i].setLRU(0);
                    updateLRU(row, i);
                    print_log_entry(name, "SW", pc, address, row);
                    return false;
                }
            }
            // Miss with eviction
            for (size_t i = 0; i < assoc; ++i) {
                if (cacheBlock[row][i].getValid()) {
                    if (cacheBlock[row][i].getLRU() >= cacheBlock[row][final].getLRU()) {
                        cacheBlock[row][i].setTag(tag);
                        final = i;
                    }
                }
            }
            updateLRU(row, final);
            print_log_entry(name, "SW", pc, address, row);
            return false;

        } else {  // For other operations
            // Hit
            for (size_t i = 0; i < assoc; ++i) {
                if (cacheBlock[row][i].getValid())
                    if (cacheBlock[row][i].getTag() == tag) {
                        updateLRU(row, i);
                        print_log_entry(name, "HIT", pc, address, row);
                        return true;
                    }
            }
            // Miss
            for (size_t i = 0; i < assoc; ++i) {
                if (!cacheBlock[row][i].getValid()) {
                    cacheBlock[row][i].setValid(true);
                    cacheBlock[row][i].setTag(tag);
                    cacheBlock[row][i].setLRU(0);
                    updateLRU(row, i);
                }
            }
            // Miss with eviction
            for (size_t i = 0; i < assoc; ++i) {
                if (cacheBlock[row][i].getValid()) {
                    if (cacheBlock[row][i].getLRU() >= cacheBlock[row][final].getLRU()) {
                        cacheBlock[row][i].setTag(tag);
                        final = i;
                    }
                }
            }
            updateLRU(row, final);
            print_log_entry(name, "MISS", pc, address, row);
            return false;
        }
    }
};

uint16_t execute(uint16_t mc[],Cache& L1, Cache* L2 = nullptr);



//three reg instructions

uint16_t add(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst);
uint16_t sub(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst);
uint16_t orf(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst);
uint16_t andf(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst);
uint16_t slt(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst);
uint16_t jr(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst);


//two Reg Instructions

uint16_t slti(uint16_t pc, uint16_t regA,uint16_t regB,int immData);
uint16_t lw(uint16_t mc[],uint16_t pc, uint16_t regA,uint16_t regB,int immData,Cache& L1, Cache* L2);
uint16_t sw(uint16_t mc[],uint16_t pc, uint16_t regA,uint16_t regB,int immData, Cache& L1, Cache* L2);
uint16_t jeq(uint16_t pc, uint16_t regA,uint16_t regB,int immData);
uint16_t addi(uint16_t pc, uint16_t regA,uint16_t regB,int immData);

//No Reg

uint16_t j(uint16_t pc, uint16_t imm);
uint16_t jal(uint16_t pc, uint16_t imm);

/*
    Prints out the correctly-formatted configuration of a cache.

    @param cache_name The name of the cache. "L1" or "L2"

    @param size The total size of the cache, measured in memory cells.
        Excludes metadata

    @param assoc The associativity of the cache. One of [1,2,4,8,16]

    @param blocksize The blocksize of the cache. One of [1,2,4,8,16,32,64])

    @param num_rows The number of rows in the given cache.
*/
void print_cache_config(const string &cache_name, int size, int assoc, int blocksize, int num_rows) {
    cout << "Cache " << cache_name << " has size " << size <<
        ", associativity " << assoc << ", blocksize " << blocksize <<
        ", rows " << num_rows << endl;
}

/*
    Prints out a correctly-formatted log entry.

    @param cache_name The name of the cache where the event
        occurred. "L1" or "L2"

    @param status The kind of cache event. "SW", "HIT", or
        "MISS"

    @param pc The program counter of the memory
        access instruction

    @param addr The memory address being accessed.

    @param row The cache row or set number where the data
        is stored.
*/


/**
    Main function
    Takes command-line args as documented below
*/
int main(int argc, char *argv[]) {
    /*
        Parse the command-line arguments
    */
    char *filename = nullptr;
    bool do_help = false;
    bool arg_error = false;
    string cache_config;
    for (int i=1; i<argc; i++) {
        string arg(argv[i]);
        if (arg.rfind("-",0)==0) {
            if (arg== "-h" || arg == "--help")
                do_help = true;
            else if (arg=="--cache") {
                i++;
                if (i>=argc)
                    arg_error = true;
                else
                    cache_config = argv[i];
            }
            else
                arg_error = true;
        } else {
            if (filename == nullptr)
                filename = argv[i];
            else
                arg_error = true;
        }
    }
    /* Display error message if appropriate */
    if (arg_error || do_help || filename == nullptr) {
        cerr << "usage " << argv[0] << " [-h] [--cache CACHE] filename" << endl << endl;
        cerr << "Simulate E20 cache" << endl << endl;
        cerr << "positional arguments:" << endl;
        cerr << "  filename    The file containing machine code, typically with .bin suffix" << endl<<endl;
        cerr << "optional arguments:"<<endl;
        cerr << "  -h, --help  show this help message and exit"<<endl;
        cerr << "  --cache CACHE  Cache configuration: size,associativity,blocksize (for one"<<endl;
        cerr << "                 cache) or"<<endl;
        cerr << "                 size,associativity,blocksize,size,associativity,blocksize"<<endl;
        cerr << "                 (for two caches)"<<endl;
        //return 1;
    }

    ifstream f(filename);
    if (!f.is_open()) {
        cerr << "Can't open file "<<filename<<endl;
        return 1;
    }
    uint16_t machinecode[MEM_SIZE]={0}; //machine code array
    load_machine_code(f,machinecode);
    size_t pc = 0;
    /* parse cache config */
//    cout<<"before"<<endl;
//    cout<<cache_config.size()<<endl;
    if (cache_config.size() > 0) {
        //cout<<"after"<<endl;
        vector<int> parts;
        size_t pos;
        size_t lastpos = 0;
        while ((pos = cache_config.find(",", lastpos)) != string::npos) {
            parts.push_back(stoi(cache_config.substr(lastpos,pos)));
            lastpos = pos + 1;
        }
        parts.push_back(stoi(cache_config.substr(lastpos)));
        if (parts.size() == 3) {
            //cout<<"HI"<<endl;
            int L1size =parts[0];
            int L1assoc = parts[1];
            int L1blocksize = parts[2];
            int L1row = L1size/(L1assoc*L1blocksize);
            print_cache_config("L1",L1size,L1assoc,L1blocksize,L1row);
            Cache L1("L1",L1size,L1assoc,L1blocksize,L1row);;//just to pass as a parameter inst
            pc = execute(machinecode,L1);
            // TODO: execute E20 program and simulate one cache here
        } else if (parts.size() == 6) {
            //cout<<"HI"<<endl;
            int L1size = parts[0];
            int L1assoc = parts[1];
            int L1blocksize = parts[2];
            int L1row = L1size/(L1assoc*L1blocksize);
            int L2size = parts[3];
            int L2assoc = parts[4];
            int L2blocksize = parts[5];
            int L2row = L2size/(L2assoc*L2blocksize);

            print_cache_config("L1",L1size,L1assoc,L1blocksize,L1row);
            print_cache_config("L2",L2size,L2assoc,L2blocksize,L2row);
            Cache L1("L1",L1size,L1assoc,L1blocksize,L1row);
            Cache L2("L2",L2size,L2assoc,L2blocksize,L2row);
            pc = execute(machinecode,L1,&L2);
            // TODO: execute E20 program and simulate two caches here
        } else {
            //cout<< "HI"<<endl;
            cerr << "Invalid cache config"  << endl;
            return 1;
        }
    }

    //uint16_t pc = execute(machinecode);
    //cout<<"hi"<<endl;
    return 0;
}



uint16_t execute(uint16_t mc[],Cache& L1, Cache* L2){//011000000011
    uint16_t pc=0; //program counter init at 0
    uint16_t curr=0; //a val to check previous pc value in loop
    bool end = false;// a val to end the loop
    while (!end) //while end is not true
    {
        uint16_t oppCode = mc[pc&8191] >> 13; //bit shifting to get oppcode
        //100000000000000>>000000000000000100


        //3 regs args and 4 bit imm
        //opcode 000
        if (oppCode == 0){ //add, sub, or, and, slt, jr
            //all bit shifts to extract registers and imm
            uint16_t RegA = (mc[pc&8191] << 3);
            RegA = RegA >> 13;
            uint16_t RegB = (mc[pc&8191] << 6);
            RegB = RegB >> 13;
            uint16_t RegDst = (mc[pc&8191] << 9);
            RegDst = RegDst >> 13;
//            uint16_t immData = (mc[pc&8191] << 12);
//            immData = immData >> 12;//imm is unsigned so no need to convert to twos comp
            uint16_t immData = mc[pc&8191] & 0b1111;
            //for slt
//            int16_t immData2 = (mc[pc] << 12); //notice that the type is int and not unint
//            immData2 = immData2 >> 12; //still this value is the unsigned value
//
//            //Here the imm is signed so I need to convert to twos compliment
//            int twoimm2 = immData2;
//            if (immData2 >= 128){ //checking if 7th least sig bit is 1
//                twoimm2=-64 +(immData2-128); //if it is then convert to signed
//            }
//

            if (immData == 0){
                //call add func
                pc = add(pc,RegA,RegB,RegDst);
            }
            if (immData == 1){
                //call sub
                pc = sub(pc,RegA,RegB,RegDst);
            }
            if (immData == 2){
                //call or
                pc = orf(pc,RegA,RegB,RegDst);
            }
            if (immData == 3){
                //call and
                pc = andf(pc,RegA,RegB,RegDst);
            }
            if (immData == 4){
                //call slt}
                pc = slt(pc,RegA,RegB,RegDst);
            }
            if (immData == 8){
                //call jr
                pc = jr(pc,RegA,RegB,RegDst);
            }
        }


            //no reg args
            //010
            //011
        else if (oppCode == 2){ // call j
            uint16_t immData = (mc[pc&8191] << 3);
            immData = immData >> 3;

            pc = j(pc,immData);
        }


        else if (oppCode == 3){ // call jal
            uint16_t immData = (mc[pc&8191] << 3);
            immData = immData >> 3;

            pc = jal(pc,immData);
        }


        else{//2 reg args and 7 bit imm
            //slti, lw, sw, jeq, addi
            uint16_t RegA = (mc[pc&8191] << 3);
            RegA = RegA >> 13;
            uint16_t RegB = (mc[pc&8191] << 6);
            RegB = RegB >> 13;
            int16_t immData = (mc[pc&8191] << 9); //notice that the type is int and not unint
            immData = immData >> 9; //still this value is the unsigned value

            //Here the imm is signed so I need to convert to twos compliment
            int twoimm=immData;
            if (immData >= 128){ //checking if 7th least sig bit is 1
                twoimm=-64 +(immData-128); //if it is then convert to signed
            }
            if (oppCode == 7){
                //call slti
                pc = slti(pc,RegA,RegB,twoimm);
            }
            if (oppCode == 4){
                //call lw
                    pc = lw(mc,pc,RegA,RegB,twoimm, L1, L2);
            }
            if (oppCode == 5){
                //call sw
                pc = sw(mc,pc,RegA,RegB,twoimm,L1,L2);
            }
            if (oppCode == 6){
                //call jeq
                pc = jeq(pc,RegA,RegB,twoimm);

            }
            if (oppCode == 1){
                //call addi
                pc = addi(pc,RegA,RegB,twoimm);

            }
        }
        registers[0]=0; //Make sure $0 is not changed after every line
        //If it is, is not an error it just does nothing
        if (curr == pc && oppCode == 2 ) { //ending the loop if there is a halt
            //halt is also equivalent to jumping to the same address which is where curr comes to play
            end=true; //setting loop end val to true
        }
        curr=pc; //setting the curr val to the pc val so we can check if the next iteration is a halt
    }
    //Personal Notes
//while true
//check oppcode switch statement right shift 13 oppcode = mc[i]>>13
//hardcode if statements
//pc++ if not a jump
//stop when program
//halt= j to pc
//if pc is the same and opp code is j
//Returning PC
    return pc;
}


//These instructions take in the pc counter and return a pc counter

//three reg instructions

uint16_t add(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst){ //Three registers
    //cout<<"add"<<endl;
    registers[regDst] = registers[regA] + registers[regB];
    pc+=1;
    return pc;
}
uint16_t sub(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst){//Three registers
    //cout<<"sub"<<endl;
    registers[regDst] = registers[regA] - registers[regB];
    pc+=1;
    return pc;
}
uint16_t orf(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst){
    //Three registers or is built in so name is orf
    //cout<<"or"<<endl;
    registers[regDst] = registers[regA] | registers[regB];
    pc+=1;
    return pc;
}
uint16_t andf(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst){
    //Three registers and is built in so name is andf
    //cout<<"and"<<endl;
    registers[regDst] = registers[regA] & registers[regB];
    pc+=1;
    return pc;
}
uint16_t slt(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst){//Three registers
    //cout<<"slt"<<endl;
    if (registers[regA] < registers[regB]){
        registers[regDst] = 1;
    }
    else{
        registers[regDst] = 0;
    }
    pc+=1;
    return pc;
}
uint16_t jr(uint16_t pc, uint16_t regA,uint16_t regB,uint16_t regDst){//Three registers
    //cout<<"jr"<<endl;
    pc = registers[regA];
    return pc;
}


//These Instructions take two regs and a 7 bit imm data

//two Reg Instructions

uint16_t slti(uint16_t pc, uint16_t regA,uint16_t regB,int immData){ //Take in an int imm because the imm is signed
    //cout<<"slti"<<endl;
    if (registers[regA] < immData){
        registers[regB] = 1;
    }
    else{registers[regB] = 0;}
    pc+=1;
    return pc;
}
uint16_t lw(uint16_t mc[], uint16_t pc, uint16_t regA,uint16_t regB,int immData,Cache &L1, Cache* L2 = nullptr){
    //cout<<"lw"<<endl;

    uint16_t newadd = registers[regA] + immData;
    //L1 is always called
    //L2 is only called in LW when its passed in and L1 is a miss
    bool L1acc = L1.cacheaccess(newadd, pc,false);
    if (L2 != nullptr && L1acc == false) {
        bool L2acc = L2->cacheaccess(newadd, pc,false);
    }

    registers[regB]= mc[registers[regA] + immData];
    pc+=1;
    return pc;
}
uint16_t sw(uint16_t mc[], uint16_t pc, uint16_t regA,uint16_t regB,int immData, Cache &L1, Cache* L2 = nullptr){
    //cout<<"sw"<<endl;
    uint16_t newadd = registers[regA]+immData;
    bool L1acc = L1.cacheaccess(newadd, pc,true);
    //L2 is always called if passed in regardless if its a miss or hit
    if(L2 != nullptr) {
        bool L2acc = L2->cacheaccess(newadd, pc,true);
    }
    mc[registers[regA]+immData] = registers[regB];
    pc+=1;
    return pc;
}
uint16_t jeq(uint16_t pc, uint16_t regA,uint16_t regB,int immData){
    //cout << "jeq" <<endl;
    if (registers[regA] == registers[regB]){
        pc+=1+immData;
        return pc;
    }
    pc+=1;
    return pc;
}
uint16_t addi(uint16_t pc, uint16_t regA,uint16_t regB,int immData){
    //cout << "addi" << endl;
    registers[regB] = registers[regA] + immData;
    pc+=1;
    return pc;
}


//No Reg

uint16_t j(uint16_t pc, uint16_t imm){ //Jumps to pc
    //cout<< "j" <<endl;
    pc = imm;
    return pc;
}
uint16_t jal(uint16_t pc, uint16_t imm){ //$7 is pc+1 and pc is the imm
    //cout<< "JAL" <<endl;
    registers[7] = pc + 1;
    pc = imm;
    return pc;
}
