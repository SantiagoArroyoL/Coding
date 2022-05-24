package ciencias.unam.practica04.api.service;

import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import ciencias.unam.practica04.api.entity.Category;
import ciencias.unam.practica04.api.repository.RepoCategory;

@Service
public class SvcCategoryImp implements SvcCategory {

    @Autowired
    RepoCategory repo;

    @Override
    public List<Category> getCategories() {
        return repo.findByStatus(1);
    }

    @Override
    public Category getCategory(Integer category_id) {
        return repo.findByCategoryId(category_id);
    }

    @Override
    public String createCategory(Category category) {
        Category saved = (Category) repo.findByCategory(category.getCategory());
        if (saved != null)
            if (saved.getStatus() == 0) {
                repo.activateCategory(saved.getCategory_id());
                return "category has been activated";
            } else
                return "category already exists";
        repo.createCategory(category.getCategory());
        return "category created";
    }

    @Override
    public String updateCategory(Integer category_id, Category category) {
        Category saved = (Category) repo.findByCategoryId(category_id);
        if (saved == null)
            return "category does not exist";
        else
            if (saved.getStatus() == 0)
                return "category is not active";
            else {
                saved = (Category) repo.findByCategory(category.getCategory());
                if (saved != null)
                    return "category already exists";
                repo.updateCategory(category_id, category.getCategory());
                return "category updated";
            }
    }

    @Override
    public String deleteCategory(Integer category_id) {
        Category saved = (Category) repo.findByCategoryId(category_id);
        if (saved == null)
            return "category does not exist";
        else {
            repo.deleteById(category_id);
            return "category removed";
        }
    }
    
}
