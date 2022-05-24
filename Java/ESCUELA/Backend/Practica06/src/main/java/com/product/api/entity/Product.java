package com.product.api.entity;

import javax.persistence.Id;
import javax.persistence.JoinColumn;
import javax.persistence.OneToOne;
import javax.persistence.Table;
import javax.persistence.CascadeType;
import javax.persistence.Column;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.validation.constraints.Max;
import javax.validation.constraints.Min;
import javax.persistence.Transient;
import javax.validation.constraints.NotNull;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;

@Entity
@Table(name = "product")
public class Product {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @JsonProperty("product_id")
    @Column(name = "product_id")
    private int product_id;

    @JsonProperty("gtin")
    @NotNull(message = "gtin is required")
    @Column(name = "gtin")
    private String gtin;

    @JsonProperty("product")
    @NotNull(message = "product is required")
    @Column(name = "product")
    private String product;

    @JsonProperty("description")
    @Column(name = "description")
    private String description;

    @JsonProperty("price")
    @NotNull(message = "price is required")
    @Column(name = "price")
    private Double price;

    @JsonProperty("stock")
    @NotNull(message = "stock is required")
    @Column(name = "stock")
    private int stock;

    @JsonProperty("category_id")
    @NotNull(message = "category_id is required")
    @Column(name = "category_id")
    private Integer category_id;

    @OneToOne(cascade = CascadeType.ALL)
    @JoinColumn(name = "product_image_id", referencedColumnName = "product_image_id")
    private ProductImage productImage;

    @Column(name = "status")
    @Min(value = 0, message = "status must be 0 or 1")
    @Max(value = 1, message = "satus must be 0 or 1")
    @JsonIgnore
    private Integer status;

    @Transient
    @JsonProperty("category")
    private Category category;

    public Product() {

    }

    public int getProduct_id() {
        return this.product_id;
    }

    public Integer getCategory_id() {
        return this.category_id;
    }

    public void setCategory_id(Integer category_id) {
        this.category_id = category_id;
    }

    public void setProduct_id(int product_id) {
        this.product_id = product_id;
    }

    public String getGtin() {
        return this.gtin;
    }

    public void setGtin(String gtin) {
        this.gtin = gtin;
    }

    public String getProduct() {
        return this.product;
    }

    public void setProduct(String product) {
        this.product = product;
    }

    public String getDescription() {
        return this.description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public Double getPrice() {
        return this.price;
    }

    public void setPrice(Double price) {
        this.price = price;
    }

    public int getStock() {
        return this.stock;
    }

    public void setStock(int stock) {
        this.stock = stock;
    }

    public Category getCategory() {
        return this.category;
    }

    public void setCategory(Category category) {
        this.category = category;
    }

    public ProductImage getProductImage() {
        return this.productImage;
    }

    public void setProductImage(ProductImage productImage) {
        this.productImage = productImage;
    }

    public int getStatus() {
        return this.status;
    }

    public void setStatus(int status) {
        this.status = status;
    }

}
