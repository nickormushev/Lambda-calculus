#include <cstdio>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <random>
#include <algorithm>
#include <exception>
#include <stack>

//Example lambda term syntax z\x(x\y(xyt))qq\s(t\p(sq))
//struct notEnoughLettersException: public std::exception {
    //const char * what() const noexcept override {
        //return "The lambda term could not be generated due the there not being enough letters in the english alphabet";
    //}
//};

std::string extractVariable(std::string str, size_t& i) {
    std::string res;

    while(str[i] != '`') {
        res.push_back(str[i++]);
    }

    return res;
}

//Decrements lambda counter of exiting a lambda
void checkBracketCounter(int& lambdaCounter, std::stack<char>& bracketStack) {

    if(bracketStack.empty()) {
        return;
    }

    if(bracketStack.top() == 'l'){
        lambdaCounter--;
    } 

    bracketStack.pop();
}

std::map<std::string, int> mapCharsToNums(std::string term) {
    int lambdaCounter = 0;
    int freeVarCount = 0;
    std::stack<char> bracketStack;
    std::map<std::string, int> baf;

    for (size_t i = 0; i < term.length(); i++) {
        if(term[i] == '(') {
            i++;
            bracketStack.push('(');
        }

        if(term[i] == ')') {
            checkBracketCounter(lambdaCounter, bracketStack);
        } else if(term[i] == '\\') {
            lambdaCounter++;
            bracketStack.pop();
            bracketStack.push('l');

            //Skip backtick and backslash
            i += 2;

            std::string boundedVar = extractVariable(term, i);
            baf[boundedVar] = -lambdaCounter;
        } else if(term[i] == '`') {
            i++;
            std::string possibleFreeVariable = extractVariable(term, i);

            if(baf[possibleFreeVariable] == 0) {
                baf[possibleFreeVariable] = freeVarCount++;
            }
        }
    }

    return baf;
}


//Lambda to De Brujn
std::string lamToDb(std::string term) {
    std::map<std::string, int> stringToNum = mapCharsToNums(term);
    int lambdaCounter = 0;
    std::stack<char> bracketStack;
    std::string dbTerm;

    for (std::pair<std::string,int> i : stringToNum) {
        std::cout << i.first << " " << i.second << std::endl;
    }

    for (size_t i = 0; i < term.length(); ++i) {
        if(term[i] == '(') {
            dbTerm.push_back('(');
            //A term should not end with an opening bracket
            bracketStack.push('(');
        } else if(term[i] == ')') {
            checkBracketCounter(lambdaCounter, bracketStack);
            dbTerm.push_back(')');
        } else if(term[i] == '\\') {
            dbTerm.push_back('\\');
            //Skip the letter after the lambda
            i+=2;
            extractVariable(term, i);
            lambdaCounter++;  
            //If I have seen a '(' I have pushed it on the stack.
            //I need to pop it and the push a lambda
            bracketStack.pop();
            bracketStack.push('l');
        } else if(term[i] == '`') {
            std::string var = extractVariable(term, ++i);
            dbTerm.push_back(stringToNum[var] + lambdaCounter + '0');
        }
    }

    return dbTerm;
}

//Generates the nth letter in the english alphabet
std::string generateChar(int& n) {
    return "x" + std::to_string(n++);
}

void checkTermSymbol(char x, std::string& lambdaTerm, int& lambdaCounter, std::stack<char>& bracketStack,
            std::map<int, std::string>& numToChar, int& letterCount) {

    if(x == '(') {
        lambdaTerm.push_back('(');
        bracketStack.push('(');
    } else if(x == ')') {
        checkBracketCounter(lambdaCounter, bracketStack);
        lambdaTerm.push_back(')');
    } else if(x == '\\') {
        //If we enter a new lambda the boundedVar at the lambdaCounter receives a new char mapped to it
        //And we add it and the lambda to the term
        std::string newLambdaVar = generateChar(letterCount);
        lambdaCounter++;
        numToChar[-lambdaCounter] = newLambdaVar;

        //Removes the '(' read when reading the '(' and adds a lambda instead
        bracketStack.pop();
        bracketStack.push('l');

        lambdaTerm.append("\\`" + newLambdaVar + "`");
    } else {
        int number = (x - '0') - lambdaCounter;

        if(number >= 0 && numToChar.find(number) == numToChar.end()) {
            numToChar[number] = generateChar(letterCount);
        } 
        
        lambdaTerm.append("`" + numToChar[number] + "`");
    }
}

//De brujn to lambda
std::string dbToLam(std::string term) { int lambdaCounter = 0; int letterCount = 0;
    std::map<int, std::string> numToChar;
    std::stack<char> bracketStack;
    std::string lamTerm;

    for (size_t i = 0; i < term.length(); ++i) {
        checkTermSymbol(term[i], lamTerm, lambdaCounter, bracketStack, numToChar, letterCount);
    }

    return lamTerm;
}

int main(void) {
    std::string term;
    int direction;

    std::cout << "For lambda term ot De Brujn term press 1" << std::endl;
    std::cout << "For the reverse press 2" << std::endl;
    std::cin >> direction;
    std::cout << "Enter term" << std::endl;
    std::cin >> term;

    if(direction == 1) {
        std::cout << lamToDb(term) << std::endl;
    } else if(direction == 2) {
        std::cout << dbToLam(term) << std::endl;
    }

    return 0;
}
