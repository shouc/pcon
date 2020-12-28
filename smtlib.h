//
// Created by shou on 12/26/20.
//

#ifndef PCON_SMTLIB_H
#define PCON_SMTLIB_H
#include <iostream>
#include <sstream>
#include <fstream>

class smt {

public:

    std::ostringstream sink;
    smt() {
    }
#define comment_arg , const unsigned int comment=-1
#define end_with_comment if (comment != -1) sink << ");" << comment << "\n"; \
    else sink << ")";

    void declare_const(const std::string& var_name,
                       const std::string& type comment_arg){
        sink << "(declare-const " << var_name << " " << type;
        end_with_comment
    }

    void add_equal(const std::string& v_left,
                   const std::string& v_right comment_arg){
        sink << "(assert (=( " << v_left << " " << v_right << ")";
        end_with_comment
    }

    void add_equal(const std::string& v_left,
                   const long& v_right comment_arg){
        sink << "(assert (=( " << v_left << " " << v_right << ")";
        end_with_comment
    }

    void add_equal(const std::string& v_left,
                   const bool& v_right comment_arg){
        sink << "(assert (=( " << v_left << " " << v_right << ")";
        end_with_comment
    }
    ~smt(){
        std::ofstream smt_file;
        smt_file.open ("example.txt");
        smt_file << sink.str();
        smt_file.close();
    }

};

#endif //PCON_SMTLIB_H
