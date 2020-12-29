//
// Created by shou on 12/26/20.
//

#ifndef PCON_SMTLIB_H
#define PCON_SMTLIB_H
#include <iostream>
#include <sstream>
#include <fstream>
#include <map>
#include <time.h>
#define insert_or_assign_cc17(map, offset, nval) \
    if (map.find(offset) == map.end())\
        map.emplace(offset, nval);\
    else\
        map[offset] = nval;
enum {
    PCON_IS_INT,
    PCON_IS_BOOL,
    PCON_IS_STRING
};
#define type_to_int(t) t == "Int" ? PCON_IS_INT : t == "Bool" ? PCON_IS_BOOL : PCON_IS_STRING
class smt {
    std::map<std::string, int> ptr_to_type;
    void add_type(const std::string& var_name, const std::string& _type){
        insert_or_assign_cc17(ptr_to_type, var_name, type_to_int(_type));
    }

    int get_type(const std::string& var_name){
        return ptr_to_type.find(var_name)->second;
    }
public:

    std::ostringstream sink;
    smt() {
    }
#define comment_arg , const unsigned int comment=-1
#define end_with_comment if (comment != -1) sink << ");" << comment << "\n"; \
    else sink << ")";

    void declare_const(const std::string& var_name,
                       const std::string& type comment_arg){
        add_type(var_name, type);
        sink << "(declare-const v" << var_name << " " << type;
        end_with_comment
    }

    void add_equal_expr(const std::string& v_left,
                   const std::string& v_right comment_arg){
        auto left_type = get_type(v_left);
        auto right_type = get_type(v_right);
        switch (left_type) {
            case PCON_IS_BOOL:
                switch (right_type) {
                    case PCON_IS_BOOL:
                        sink << "(assert (= v" << v_left << " v" << v_right << ")";
                        break;
                    case PCON_IS_INT:
                        sink << "(assert (ite v" << v_left << " "
                                "(!= v" << v_right << " 0) "
                                "(= v" << v_right << " 0))";
                        break;
                    case PCON_IS_STRING:
                        sink << "(assert (ite v" << v_left << " "
                                "(!= v" << v_right << " \"\") "
                                "(= v" << v_right << " \"\"))";
                        break;
                    default:
                        break;
                }
                break;
            case PCON_IS_INT:
                switch (right_type) {
                    case PCON_IS_BOOL:
                        return add_equal_expr(v_right, v_left, comment);
                    case PCON_IS_INT:
                        sink << "(assert (= v" << v_left << " v" << v_right << ")";
                        break;
                    case PCON_IS_STRING:
                        sink << "(assert (= int.to.str(v" << v_left << ") v" << v_right << ")";
                        break;
                    default:
                        break;
                }
                break;
            case PCON_IS_STRING:
                switch (right_type) {
                    case PCON_IS_BOOL:
                    case PCON_IS_INT:
                        return add_equal_expr(v_right, v_left, comment);
                    case PCON_IS_STRING:
                        sink << "(assert (= v" << v_left << " v" << v_right << ")";
                        break;
                    default:
                        break;
                }
                break;
            default:
                break;
        }
        end_with_comment
    }

    void add_equal(const std::string& v_left,
                   const long& v_right comment_arg){
        auto left_type = get_type(v_left);
        switch (left_type) {
            case PCON_IS_BOOL:
                sink << "(assert (ite v" << v_left << " "
                        "(!= v" << v_right << " 0) "
                        "(= v" << v_right << " 0))";
                break;
            case PCON_IS_INT:
                sink << "(assert (= v" << v_left << " " << v_right << ")";
                break;
            case PCON_IS_STRING:
                sink << "(assert (= v" << v_left << " \"" << v_right << "\")";
                break;
            default:
                assert(0);
        }
        end_with_comment
    }

    void add_equal(const std::string& v_left,
                   const bool& v_right comment_arg){
        auto left_type = get_type(v_left);
        switch (left_type) {
            case PCON_IS_BOOL:
                sink << "(assert (= v" << v_left << " " << v_right << ")";
            case PCON_IS_INT:
                if (v_right)
                    sink << "(assert (!= v" << v_left << " 0)";
                else
                    sink << "(assert (= v" << v_left << " 0)";
                break;
            case PCON_IS_STRING:
                if (v_right)
                    sink << "(assert (!= v" << v_left << " \"\")";
                else
                    sink << "(assert (= v" << v_left << " \"\")";
                break;
            default:
                assert(0);
        }
        end_with_comment
    }


    void add_nequal_expr(const std::string& v_left,
                        const std::string& v_right comment_arg){
        auto left_type = get_type(v_left);
        auto right_type = get_type(v_right);
        switch (left_type) {
            case PCON_IS_BOOL:
                switch (right_type) {
                    case PCON_IS_BOOL:
                        sink << "(assert (!= v" << v_left << " v" << v_right << ")";
                        break;
                    case PCON_IS_INT:
                        sink << "(assert (ite v" << v_left << " "
                                "(= v" << v_right << " 0) "
                                "(!= v" << v_right << " 0))";
                        break;
                    case PCON_IS_STRING:
                        sink << "(assert (ite v" << v_left << " "
                                "(= v" << v_right << " \"\") "
                                "(!= v" << v_right << " \"\"))";
                        break;
                    default:
                        break;
                }
                break;
            case PCON_IS_INT:
                switch (right_type) {
                    case PCON_IS_BOOL:
                        return add_nequal_expr(v_right, v_left, comment);
                    case PCON_IS_INT:
                        sink << "(assert (!= v" << v_left << " v" << v_right << ")";
                        break;
                    case PCON_IS_STRING:
                        sink << "(assert (!= int.to.str(v" << v_left << ") v" << v_right << ")";
                        break;
                    default:
                        break;
                }
                break;
            case PCON_IS_STRING:
                switch (right_type) {
                    case PCON_IS_BOOL:
                    case PCON_IS_INT:
                        return add_nequal_expr(v_right, v_left, comment);
                    case PCON_IS_STRING:
                        sink << "(assert (!= v" << v_left << " v" << v_right << ")";
                        break;
                    default:
                        break;
                }
                break;
            default:
                break;
        }
        end_with_comment
    }

    void add_nequal(const std::string& v_left,
                   const long& v_right comment_arg){
        auto left_type = get_type(v_left);
        switch (left_type) {
            case PCON_IS_BOOL:
                sink << "(assert (ite v" << v_left << " "
                                                      "(= v" << v_right << " 0) "
                                                                            "(!= v" << v_right << " 0))";
                break;
            case PCON_IS_INT:
                sink << "(assert (!= v" << v_left << " " << v_right << ")";
                break;
            case PCON_IS_STRING:
                sink << "(assert (!= v" << v_left << " \"" << v_right << "\")";
                break;
            default:
                assert(0);
        }
        end_with_comment
    }

    void add_nequal(const std::string& v_left,
                   const bool& v_right comment_arg){
        auto left_type = get_type(v_left);
        switch (left_type) {
            case PCON_IS_BOOL:
                sink << "(assert (!= v" << v_left << " " << v_right << ")";
            case PCON_IS_INT:
                if (v_right)
                    sink << "(assert (= v" << v_left << " 0)";
                else
                    sink << "(assert (!= v" << v_left << " 0)";
                break;
            case PCON_IS_STRING:
                if (v_right)
                    sink << "(assert (= v" << v_left << " \"\")";
                else
                    sink << "(assert (!= v" << v_left << " \"\")";
                break;
            default:
                assert(0);
        }
        end_with_comment
    }

    ~smt(){
        std::ofstream smt_file;
        time_t t = time(nullptr);
        std::ostringstream fn;
        fn << "smt/" << t << ".txt";
        smt_file.open (fn.str());
        smt_file << sink.str();
        smt_file.close();
    }

};

#endif //PCON_SMTLIB_H
