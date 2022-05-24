package com.product.api.entity;

import javax.persistence.Id;
import javax.persistence.Table;
import javax.persistence.Column;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.validation.constraints.Max;
import javax.validation.constraints.Min;
import javax.validation.constraints.NotNull;

import com.fasterxml.jackson.annotation.JsonIgnore;

@Entity
@Table(name = "category")
public class Category {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @Column(name = "category_id")
    private int category_id;

    @NotNull(message = "category should not be null")
    @Column(name = "category")
    private String category;

    @Column(name = "status")
    @Min(value = 0, message = "status must be 0 or 1")
    @Max(value = 1, message = "satus must be 0 or 1")
    @JsonIgnore
    private int status;

    public Category() {

    }

    public int getCategory_id() {
        return this.category_id;
    }

    public void setCategory_id(int category_id) {
        this.category_id = category_id;
    }

    public String getCategory() {
        return this.category;
    }

    public void setCategory(String category) {
        this.category = category;
    }

    public int getStatus() {
        return this.status;
    }

    public void setStatus(int status) {
        this.status = status;
    }

    @Override
    public String toString() {
        return "Category[category_id= " + category_id + ", category= " + category + ", status= " + status + "]";
    }

}
